-- Prove2me | Definitions.Def_OAIQ106D014
-- name    : OAIQ106D014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:02:58.848218+00:00
-- url     : https://prove2.me/theorems/170b4d64-1830-44fb-8cc8-94cfbf6768e6
-- title:
--   Definitions bundle OAIQ106D014 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2131 declarations of OpenAI's Lean: 2131 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw18393step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18393step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18393step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18394`, `OAI.MUB6.Certificate.MixedSemantics.raw18394step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18394step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18394step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18394step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18395`, `OAI.MUB6.Certificate.MixedSemantics.raw18395Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18395step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18395step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18395step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18395step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18396`, `OAI.MUB6.Certificate.MixedSemantics.raw18396Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18396step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18396step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18396step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18396step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18397`, `OAI.MUB6.Certificate.MixedSemantics.raw18397Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18397step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18398`, `OAI.MUB6.Certificate.MixedSemantics.raw18398Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18398step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18398step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18398step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18398step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18399`, `OAI.MUB6.Certificate.MixedSemantics.raw18399Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18399step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18399step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18399step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18399step1Labels` and 2091 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical143`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical143.lean), [`MutuallyUnbiased_MixedSemantics_Canonical144`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical144.lean), [`MutuallyUnbiased_MixedSemantics_Canonical145`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical145.lean), [`MutuallyUnbiased_MixedSemantics_Singletons18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Singletons18.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1163`, `OAI.MUB6.Certificate.MixedSemantics.sound1475`, `OAI.MUB6.Certificate.MixedSemantics.sound1477`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1100`, `OAI.MUB6.Certificate.MixedSemantics.sourceEq1104`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound955`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound961`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43`.
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

def raw183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw183step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1848 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1849 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1850 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1850Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1863 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1864 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1865 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1865Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]

def raw18393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]

def raw18394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw18397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18408step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18410step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18411step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18413step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18414step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18417step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18418step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18419 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18423step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18424step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18429step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18433step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18434step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18435step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18436step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18437step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18444step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18452step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18453step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18454step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18455step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18456step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18457step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18458step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18459step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18460step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18473step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18474step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18478step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18479step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18483step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18484step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18486step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18488step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18489step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18490step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18495step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18500step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw18501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw18501step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw18505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18511step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18512step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18514step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18515step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18517step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18518step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18519step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18521step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18522step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18523step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18525step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18527step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18528step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18529step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18530step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18531step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18532step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18533step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18539step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18545step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18549step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18550step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw18552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18574step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18575step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18576step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18577step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18578step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18586step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18587step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18596step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18602step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18608step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw18610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18611step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18612step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18613step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18614step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18615step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18616step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18617step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18618step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18619step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18622 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw18625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18635step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18645step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw18653step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18658step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18662step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18674step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def singletonSmall1163 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


