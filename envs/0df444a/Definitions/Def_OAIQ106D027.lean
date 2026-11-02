-- Prove2me | Definitions.Def_OAIQ106D027
-- name    : OAIQ106D027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:13:04.970199+00:00
-- url     : https://prove2.me/theorems/5bc6f5cd-615a-4fa2-8da0-9d97d03abf7a
-- title:
--   Definitions bundle OAIQ106D027 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7409 declarations of OpenAI's Lean: 7409 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw31159step2`, `OAI.MUB6.Certificate.MixedSemantics.raw31159step3`, `OAI.MUB6.Certificate.MixedSemantics.raw31159step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3115Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step0`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step1`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step2`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step3`, `OAI.MUB6.Certificate.MixedSemantics.raw3115step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw3116`, `OAI.MUB6.Certificate.MixedSemantics.raw31160`, `OAI.MUB6.Certificate.MixedSemantics.raw31160Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step2`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step3`, `OAI.MUB6.Certificate.MixedSemantics.raw31160step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31161`, `OAI.MUB6.Certificate.MixedSemantics.raw31161Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31161step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31161step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31161step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31161step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31162`, `OAI.MUB6.Certificate.MixedSemantics.raw31162Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31162step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31162step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31163`, `OAI.MUB6.Certificate.MixedSemantics.raw31163Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31163step0`, `OAI.MUB6.Certificate.MixedSemantics.raw31163step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31163step1`, `OAI.MUB6.Certificate.MixedSemantics.raw31163step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw31164` and 7369 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical24`, `MutuallyUnbiased_MixedSemantics_Canonical243`, `MutuallyUnbiased_MixedSemantics_Canonical244`, `MutuallyUnbiased_MixedSemantics_Canonical245`, `MutuallyUnbiased_MixedSemantics_Canonical246`, `MutuallyUnbiased_MixedSemantics_Canonical247`, `MutuallyUnbiased_MixedSemantics_Canonical248`, `MutuallyUnbiased_MixedSemantics_Canonical249`, `MutuallyUnbiased_MixedSemantics_Canonical25`, `MutuallyUnbiased_MixedSemantics_Canonical250`, `MutuallyUnbiased_MixedSemantics_Canonical251`, `MutuallyUnbiased_MixedSemantics_Canonical252`, `MutuallyUnbiased_MixedSemantics_Canonical253`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1168`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound2957`, `OAI.MUB6.Certificate.MixedSemantics.sound2958`, `OAI.MUB6.Certificate.MixedSemantics.sound2959`, `OAI.MUB6.Certificate.MixedSemantics.sound2960`, `OAI.MUB6.Certificate.MixedSemantics.sound2961`, `OAI.MUB6.Certificate.MixedSemantics.sound2963`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound18`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1854`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1865`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1880`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1882`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound19`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1969`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1989`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1994`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound20`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2003`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2011`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2014`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2078`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2080`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound50`.
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical243
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]

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

end MUB6.Certificate.MixedSemantics

end OAI
end


