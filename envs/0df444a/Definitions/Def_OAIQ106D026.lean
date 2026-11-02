-- Prove2me | Definitions.Def_OAIQ106D026
-- name    : OAIQ106D026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:12:47.105214+00:00
-- url     : https://prove2.me/theorems/fe7832a0-803c-4dda-a9cf-c7ae02a7a3db
-- title:
--   Definitions bundle OAIQ106D026 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7471 declarations of OpenAI's Lean: 7471 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw29686step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29686step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29686step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29687`, `OAI.MUB6.Certificate.MixedSemantics.raw29687Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29687step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29688`, `OAI.MUB6.Certificate.MixedSemantics.raw29688Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29688step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29688step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29688step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29688step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29689`, `OAI.MUB6.Certificate.MixedSemantics.raw29689Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29689step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2968Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2968step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2968step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2968step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2968step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2969`, `OAI.MUB6.Certificate.MixedSemantics.raw29690`, `OAI.MUB6.Certificate.MixedSemantics.raw29690Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step0`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step1`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step2`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw29690step3` and 7431 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical23`, `MutuallyUnbiased_MixedSemantics_Canonical231`, `MutuallyUnbiased_MixedSemantics_Canonical232`, `MutuallyUnbiased_MixedSemantics_Canonical233`, `MutuallyUnbiased_MixedSemantics_Canonical234`, `MutuallyUnbiased_MixedSemantics_Canonical235`, `MutuallyUnbiased_MixedSemantics_Canonical236`, `MutuallyUnbiased_MixedSemantics_Canonical237`, `MutuallyUnbiased_MixedSemantics_Canonical238`, `MutuallyUnbiased_MixedSemantics_Canonical239`, `MutuallyUnbiased_MixedSemantics_Canonical24`, `MutuallyUnbiased_MixedSemantics_Canonical240`, `MutuallyUnbiased_MixedSemantics_Canonical241`, `MutuallyUnbiased_MixedSemantics_Canonical242`, `MutuallyUnbiased_MixedSemantics_Canonical243`, `MutuallyUnbiased_MixedSemantics_Canonical27`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound2904`, `OAI.MUB6.Certificate.MixedSemantics.sound2936`, `OAI.MUB6.Certificate.MixedSemantics.sound2937`, `OAI.MUB6.Certificate.MixedSemantics.sound2939`, `OAI.MUB6.Certificate.MixedSemantics.sound2941`, `OAI.MUB6.Certificate.MixedSemantics.sound2943`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound1`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound13`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound14`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1429`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1797`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1817`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1825`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1826`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1828`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1829`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1845`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1846`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1848`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1856`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1881`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1964`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2051`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2052`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2056`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound49`.
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

def raw2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw2step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw2step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw29Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw29step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw30 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
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

def raw296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw297Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw297step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw299Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw299step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw299step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
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

def raw2968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2973step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2987step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2988step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw2992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw2993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw2998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3008step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3009step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3010step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3012step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3013step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3014step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3014step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3015step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3018step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3018step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw3023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29711 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw29711Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29711step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw29711step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29711step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw29711step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29712 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw29759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw29781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw29786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw29794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw29795step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw29799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw29809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29860 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw29860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw29862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw29862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw29864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw29864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw29864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw29865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw29865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw29865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw29866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw29866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw29866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29867 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![3, -3], ![1, -1]]
def raw29867step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29867step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29867step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29867step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw29898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw29898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw29899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29900 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw29900Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw29900step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw29900step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29900step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29900step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw29905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw29905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw29906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29907 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw29907Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw29907step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw29907step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29907step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw29907step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw29908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw29909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw29911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw29911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw29914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw29931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29933 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw29933Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29933step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw29933step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29936step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw29937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 1, -3], ![2, -2, 0]]
def raw29939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw29941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw29942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, 0, -3], ![2, -2, 0]]
def raw29942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw29942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29944 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3], ![0, 0]]
def raw29944Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3]]
def raw29944step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]
def raw29944step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw29944step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29944step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29944step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29944step4Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical234
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29994step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw29996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29999step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30005step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw30005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw30014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30015step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw30018step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30019step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw30024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30075 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30075step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical235
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw30094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw30095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw30096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw30117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw30218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw30220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw30220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw30221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw30222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw30223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30224 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw30224Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30224step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30224step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw30265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30266step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30267step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30267step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw30268step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30269step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30274step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30274step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30275step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30275step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30275step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30275step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30276step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30279step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30279step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw30281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw30281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw30282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw30282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw30287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw30287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30288step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw30289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw31159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw3517Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


