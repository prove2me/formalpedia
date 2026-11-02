-- Prove2me | Definitions.Def_OAIQ106D028
-- name    : OAIQ106D028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:14:45.2247+00:00
-- url     : https://prove2.me/theorems/be71b3ad-2f66-42e8-be43-8b2aacecd7cb
-- title:
--   Definitions bundle OAIQ106D028 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7337 declarations of OpenAI's Lean: 7337 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw3243step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3243step1`, `OAI.MUB6.Certificate.MixedSemantics.raw3243step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3244`, `OAI.MUB6.Certificate.MixedSemantics.raw32440`, `OAI.MUB6.Certificate.MixedSemantics.raw32440Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32440step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32440step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32441`, `OAI.MUB6.Certificate.MixedSemantics.raw32441Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32441step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32441step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32441step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32441step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32442`, `OAI.MUB6.Certificate.MixedSemantics.raw32442Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32442step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32442step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32442step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32442step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32443`, `OAI.MUB6.Certificate.MixedSemantics.raw32443Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32443step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32443step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32443step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32443step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32444`, `OAI.MUB6.Certificate.MixedSemantics.raw32444Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32444step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32444step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32444step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32444step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32445`, `OAI.MUB6.Certificate.MixedSemantics.raw32445Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step0`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step1`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step2`, `OAI.MUB6.Certificate.MixedSemantics.raw32445step2Labels` and 7297 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical25`, `MutuallyUnbiased_MixedSemantics_Canonical253`, `MutuallyUnbiased_MixedSemantics_Canonical254`, `MutuallyUnbiased_MixedSemantics_Canonical255`, `MutuallyUnbiased_MixedSemantics_Canonical256`, `MutuallyUnbiased_MixedSemantics_Canonical257`, `MutuallyUnbiased_MixedSemantics_Canonical258`, `MutuallyUnbiased_MixedSemantics_Canonical259`, `MutuallyUnbiased_MixedSemantics_Canonical26`, `MutuallyUnbiased_MixedSemantics_Canonical260`, `MutuallyUnbiased_MixedSemantics_Canonical261`, `MutuallyUnbiased_MixedSemantics_Canonical262`, `MutuallyUnbiased_MixedSemantics_Canonical263`, `MutuallyUnbiased_MixedSemantics_Canonical264`, `MutuallyUnbiased_MixedSemantics_Singletons19`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSemantics.sound2965`, `OAI.MUB6.Certificate.MixedSemantics.sound2966`, `OAI.MUB6.Certificate.MixedSemantics.sound2968`, `OAI.MUB6.Certificate.MixedSemantics.sound2969`, `OAI.MUB6.Certificate.MixedSemantics.sound2986`, `OAI.MUB6.Certificate.MixedSemantics.sound2987`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound96`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound152`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1942`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1945`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1950`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1953`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1954`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1956`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1957`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1977`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2015`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2092`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2093`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound25`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound29`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound590`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound750`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound993`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound26` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound36`.
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical253
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall1255 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


