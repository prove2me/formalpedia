-- Prove2me | Definitions.Def_OAIQ106D030
-- name    : OAIQ106D030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:14:56.664237+00:00
-- url     : https://prove2.me/theorems/b1387436-bd0d-4e4e-9f8f-6ed4c684cae3
-- title:
--   Definitions bundle OAIQ106D030 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4943 declarations of OpenAI's Lean: 4943 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw34999step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw349Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw349step0`, `OAI.MUB6.Certificate.MixedSemantics.raw349step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34step0`, `OAI.MUB6.Certificate.MixedSemantics.raw34step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw34step1`, `OAI.MUB6.Certificate.MixedSemantics.raw34step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35`, `OAI.MUB6.Certificate.MixedSemantics.raw350`, `OAI.MUB6.Certificate.MixedSemantics.raw35000`, `OAI.MUB6.Certificate.MixedSemantics.raw35000Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35000step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35000step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35000step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35000step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35001`, `OAI.MUB6.Certificate.MixedSemantics.raw35001Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35001step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35002`, `OAI.MUB6.Certificate.MixedSemantics.raw35002Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step2`, `OAI.MUB6.Certificate.MixedSemantics.raw35002step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35003`, `OAI.MUB6.Certificate.MixedSemantics.raw35003Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35003step0`, `OAI.MUB6.Certificate.MixedSemantics.raw35003step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35003step1`, `OAI.MUB6.Certificate.MixedSemantics.raw35003step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw35003step2` and 4903 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical27`, `MutuallyUnbiased_MixedSemantics_Canonical273`, `MutuallyUnbiased_MixedSemantics_Canonical274`, `MutuallyUnbiased_MixedSemantics_Canonical275`, `MutuallyUnbiased_MixedSemantics_Canonical276`, `MutuallyUnbiased_MixedSemantics_Canonical277`, `MutuallyUnbiased_MixedSemantics_Canonical278`, `MutuallyUnbiased_MixedSemantics_Canonical279`, `MutuallyUnbiased_MixedSemantics_Canonical28`, `MutuallyUnbiased_MixedSemantics_Canonical280`, `MutuallyUnbiased_MixedSemantics_Canonical281`, `MutuallyUnbiased_MixedSemantics_Singletons18`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1161`, `OAI.MUB6.Certificate.MixedSemantics.sound1170`, `OAI.MUB6.Certificate.MixedSemantics.sound2996`, `OAI.MUB6.Certificate.MixedSemantics.sound2997`, `OAI.MUB6.Certificate.MixedSemantics.sound2998`, `OAI.MUB6.Certificate.MixedSemantics.sound3003`, `OAI.MUB6.Certificate.MixedSemantics.sound3005`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2041`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2045`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2047`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2050`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2052`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2061`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2063`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2064`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2065`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2068`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2069`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2070`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound37`.
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
def raw356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw357 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 2, -3], ![-2, 2, 0]]
def raw357Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw357step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]

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
def raw3565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw3565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw3566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw3566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw3567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw3567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw3568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw3568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw3569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw3573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw3574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw3578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw3579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![3, -3, 0]]
def raw3582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw3583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw35671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw35672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw35677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35678step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35678step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35678step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35680step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35681step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35693step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35694step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35695step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw35699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35705step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35707step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35707step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35707step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35711step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35712step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw35716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35717step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw35720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw35720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw35721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw35721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw35721step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw35722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw35726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw35726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw35726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw35727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw35727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35752step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35752step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35752step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35753step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35753step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35754step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35754step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35754step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35755step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35755step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35756step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw35761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35761step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw35764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw35765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw35765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw35767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw35767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw35768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw35768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35777step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35788step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35789step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35790step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35795step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw35797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw35799step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35799step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw35799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw35800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw35800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw35800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35809step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35813step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35813step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35815step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw35816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw35816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw35816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw35817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw35817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw35817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw3584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw3586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw3587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw3587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw3588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw3588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-4, 3, 1]]
def raw3589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw3589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw3591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw3591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![4, -4, 0]]
def raw3592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw3592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw3592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![4, -4, 0]]
def raw3593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw3593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw3593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical280
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35863step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35863step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35864step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw35864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35869step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35871step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35874step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35879step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw35883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35884step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw35888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35889step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35893step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35893step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35899step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35900step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw35907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35907step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw35908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw35909step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35909step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35909step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw35910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35910step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw35913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw35914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw35914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw35914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw35917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35917step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw35918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35946step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35946step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35947step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35947step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35947step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35948step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35948step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35948step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35949step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35950step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw35950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw35951step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw35951step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw35951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35952step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35952step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35952step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw35953step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35953step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw35953step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw35954step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35954step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw35954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35955step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35957step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35957step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35958step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35958step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35959step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35962step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35962step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35962step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw35963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35963step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35963step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35963step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35964step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35964step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw35967step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35967step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical281
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35968step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35968step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw35969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35969step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35969step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35970step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw35970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35972step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw35973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw35974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw35974step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1161 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


