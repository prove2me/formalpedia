-- Prove2me | Definitions.Def_OAIQ106D032
-- name    : OAIQ106D032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:17:11.497288+00:00
-- url     : https://prove2.me/theorems/66ee19a9-2bd6-46d4-93d4-ba825dcf0628
-- title:
--   Definitions bundle OAIQ106D032 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7605 declarations of OpenAI's Lean: 7605 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw37333step3`, `OAI.MUB6.Certificate.MixedSemantics.raw37333step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37334`, `OAI.MUB6.Certificate.MixedSemantics.raw37334Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step3`, `OAI.MUB6.Certificate.MixedSemantics.raw37334step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335`, `OAI.MUB6.Certificate.MixedSemantics.raw37335Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step3`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step4`, `OAI.MUB6.Certificate.MixedSemantics.raw37335step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336`, `OAI.MUB6.Certificate.MixedSemantics.raw37336Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step3`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step4`, `OAI.MUB6.Certificate.MixedSemantics.raw37336step4Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37337`, `OAI.MUB6.Certificate.MixedSemantics.raw37337Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37337step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37337step0Labels` and 7565 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical29`, `MutuallyUnbiased_MixedSemantics_Canonical291`, `MutuallyUnbiased_MixedSemantics_Canonical292`, `MutuallyUnbiased_MixedSemantics_Canonical293`, `MutuallyUnbiased_MixedSemantics_Canonical294`, `MutuallyUnbiased_MixedSemantics_Canonical295`, `MutuallyUnbiased_MixedSemantics_Canonical297`, `MutuallyUnbiased_MixedSemantics_Canonical298`, `MutuallyUnbiased_MixedSemantics_Canonical3`, `MutuallyUnbiased_MixedSemantics_Canonical30`, `MutuallyUnbiased_MixedSemantics_Canonical308`, `MutuallyUnbiased_MixedSemantics_Canonical309`, `MutuallyUnbiased_MixedSemantics_Canonical31`, `MutuallyUnbiased_MixedSemantics_Canonical310`, `MutuallyUnbiased_MixedSemantics_Canonical311`, `MutuallyUnbiased_MixedSemantics_Canonical312`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1172`, `OAI.MUB6.Certificate.MixedSemantics.sound1173`, `OAI.MUB6.Certificate.MixedSemantics.sound1175`, `OAI.MUB6.Certificate.MixedSemantics.sound3094`, `OAI.MUB6.Certificate.MixedSemantics.sound3099`, `OAI.MUB6.Certificate.MixedSemantics.sound3100`, `OAI.MUB6.Certificate.MixedSemantics.sound3101`, `OAI.MUB6.Certificate.MixedSemantics.sound3102`, `OAI.MUB6.Certificate.MixedSemantics.sound3106`, `OAI.MUB6.Certificate.MixedSemantics.sound3109`, `OAI.MUB6.Certificate.MixedSemantics.sound3110`, `OAI.MUB6.Certificate.MixedSemantics.sound3116`, `OAI.MUB6.Certificate.MixedSemantics.sound645`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1423`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero539`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1484`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1980`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound199`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound525`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound59`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound663`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound12`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound13`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound16`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound2`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1192` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1210`.
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

def raw3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw3step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw3step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw4 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw37Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 4, -3]]
def raw38Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw38step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw38step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw38step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw38step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw39 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 4, -3]]
def raw39Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw39step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw39step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]

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

def raw373Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw373step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw374 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]
def raw374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw374step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw375 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]
def raw375Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw375step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw375step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw376 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw377 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw377Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw377step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw378 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw379 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw379Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw379step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw380 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw380step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw381 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw381Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw381step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw382 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw382Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw382step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw382step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw383 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw383Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw383step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw383step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3817step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3822step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3822step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3822step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3834 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw3834Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3834step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw3834step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3834step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3834step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical291
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37333step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, -3, 5]]
def raw37335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 3, -5], ![-2, -3, 5]]
def raw37335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37335step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw37335step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37336 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-5, 5]]
def raw37336step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-5, 5]]
def raw37336step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![5, -5], ![-5, 5]]
def raw37336step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37336step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]
def raw37336step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37337step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37338step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37338step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -3, 5]]
def raw37339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37339step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37339step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, -3, 5]]
def raw37340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-3, -2, 5]]
def raw37340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37340step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw37340step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, -4, 5]]
def raw37341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 4, -5], ![-1, -4, 5]]
def raw37341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37341step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, -1, 5], ![4, 1, -5]]
def raw37341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw37342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37342step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw37342step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37343step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37343step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![-3, -1, 4]]
def raw37346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw37346step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37346step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw37346step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-2, -2, 4]]
def raw37347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw37347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37347step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw37347step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37348 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37348step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw37348step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37348step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw37348step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37349 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw37349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37349step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw37349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37351step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37351step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw37352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, -3, 4]]
def raw37353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw37353step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37353step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw37353step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37354step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37356step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37356step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-2, -2, 4]]
def raw37357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 1, 1], ![-2, -2, 4]]
def raw37357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37357step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw37357step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, -3, 4]]
def raw37358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-3, -1, 4]]
def raw37358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37358step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw37358step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw37370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37370step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw37370step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37372step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37373step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -3, 2], ![-3, 0, 3]]
def raw37374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw37374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37374step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw37374step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![0, -2, 2], ![-2, -1, 3]]
def raw37375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw37375step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37375step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw37375step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical292
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37376 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-2, 2], ![-3, 3]]
def raw37376step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw37376step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37377 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw37377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw37377step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37379step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw37381step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw37381step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw37382step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw37382step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw37383step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 0, 2], ![-2, -1, 3]]
def raw37391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, 0, -2], ![2, 1, -3]]
def raw37391step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37392step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-3, 0, 3]]
def raw37398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![3, 0, -3]]
def raw37398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37412 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw37412step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37413 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37447 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw37447step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37448 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw37477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw37481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37482 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37482Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37482step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37482step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37482step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37482step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37483 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37484 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw37487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw37487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37489 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw37491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw37492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical293
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37513 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37516 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw37516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw37517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw37518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37519 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw37519Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37519step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37519step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37521 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw37523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw37525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-3, -1, 4]]
def raw37530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, -1, 1], ![-3, -1, 4]]
def raw37531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw37531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37532 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37533 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, -1, 4]]
def raw37533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw37533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, -1, 4]]
def raw37534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -2, 1], ![-3, -1, 4]]
def raw37534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw37534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw37534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![-2, -2, 4]]
def raw37535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37536 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37536Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-4, 4]]
def raw37536step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-4, 4]]
def raw37536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw37536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37537 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw37538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37539 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37540 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw37540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -2, 4]]
def raw37541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-2, -2, 4]]
def raw37541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -3, 4]]
def raw37542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw37552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw37553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw37553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw37555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -3, 2], ![-3, 0, 3]]
def raw37556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw37556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw37556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -2, 2], ![-2, -1, 3]]
def raw37557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37558 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37558Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37558step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-2, 2], ![-3, 3]]
def raw37558step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37558step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw37558step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37559 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37559step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw37560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-2, 0, 2], ![0, -3, 3]]
def raw37564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37564step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw37564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw37569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw37569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw37571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -3, 2], ![-3, 0, 3]]
def raw37572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw37572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -2, 2], ![-2, -1, 3]]
def raw37573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-2, 0, 2], ![-1, -2, 3]]
def raw37574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw37574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37574step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw37577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-2, 0, 2], ![0, -3, 3]]
def raw37578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw37578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw37579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -2, 3]]
def raw37585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, -2, 2], ![-1, -2, 3]]
def raw37586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw37586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw37586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-1, -1, 2], ![0, -3, 3]]
def raw37591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw37591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw37591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 2, -1], ![-1, -1, 2], ![0, -3, 3]]
def raw37592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw37592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37593step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw37594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37621 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37621Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37621step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37621step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37621step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37621step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37623 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical294
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37647 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37647Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37647step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37647step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37647step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37647step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37648 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37653 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37654 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37655 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37656 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -2, 2], ![-3, 0, 3]]
def raw37665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -2, 2], ![-3, 0, 3]]
def raw37666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw37666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -3, 2], ![-3, 0, 3]]
def raw37669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw37669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw37669step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -2, 2], ![-2, -1, 3]]
def raw37670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37670step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37671 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37671Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37671step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-2, 2], ![-3, 3]]
def raw37671step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw37671step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw37672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw37673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw37673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-2, 0, 2], ![0, -3, 3]]
def raw37677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw37677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw37679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 0, 2], ![0, -3, 3]]
def raw37686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -2, 2], ![-2, -1, 3]]
def raw37690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw37715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw37715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37720 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37720Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37720step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37720step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37720step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37720step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw37722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw37726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw37727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw37727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37736 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37740 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37743 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37748 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical295
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw37774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw37775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw37775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37776step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37780 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37780Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37780step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37780step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37780step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37780step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw37781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37783 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw37787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw37787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37791 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37819 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37820 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37821step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37825 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37825Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37825step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37825step0Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical297
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw38091Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw38095Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical298
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw38154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw384 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw384Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw384step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw385 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw385Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw385step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw386step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw387Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw387step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw388 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw389 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 2, -2]]
def raw389Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw389step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw390 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw391 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw391Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw391step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw392 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw393 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw393Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw393step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw394 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw395 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw395Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw395step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw396 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw397 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![0, 1, -1]]
def raw397Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw397step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw398 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw399 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 2, -2]]
def raw399Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw399step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw400 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw3842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw3849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw3852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw3854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw3855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3857step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3857step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3857step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3857step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw3858step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3858step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3858step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw3858step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3858step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3873step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3876step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3876step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3878 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3879step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3880step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw3880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3881 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3895 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3895step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw3895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3898step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw3903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw3904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw3942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw3942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw3944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw3945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3945step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw3945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw3947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw3950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3950step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw3950step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw3951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw3957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw3962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw3963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw3963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw3964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw3964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw3965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw3965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw3966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw3967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw3967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw39450step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw39450step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw39451step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw39452step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39453step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39453step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39454step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39455step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39456step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39457step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39458step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39458step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw39459step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39460Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39460step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39460step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39461Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39461step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39461step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39462Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39462step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39462step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39462step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39463Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39463step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39464Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39464step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39464step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw39464step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw39464step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw39464step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39465Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39465step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39465step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39465step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39466Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39466step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39466step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39466step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39467Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39467step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39467step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39467step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39468Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39468step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39468step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39469Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39469step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39469step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39470Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39470step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw39470step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39471Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39471step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39471step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39472Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39472step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39473step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw39474step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39474step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39475step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw39475step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39476step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39476step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw39477step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw39477step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39478step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39479step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39480step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39481step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39482step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39483Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39483step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39483step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39484Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39484step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39484step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39485Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39485step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39485step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw39485step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39485step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39485step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39486Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39486step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw39486step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39486step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39487Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39487step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39487step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39488Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39488step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39488step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39489Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39489step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39489step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39490Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39490step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39490step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39491Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39491step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39491step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39492Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39492step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39492step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39493Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39493step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39493step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39494Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39494step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39494step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39495Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39495step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39496Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39496step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39497Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39497step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw39497step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39498Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39498step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39499Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39499step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39500Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39500step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39501Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39501step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39502Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39502step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39503step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39503step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39504Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39504step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39504step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39505step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39505step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw39505step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39506Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39506step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39506step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39507step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39507step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39508Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39508step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw39508step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39509step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39509step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39510Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39510step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39510step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39511Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39511step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39512Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39512step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw39513step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw39514step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw39514step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39516step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw39517step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39518step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39519step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39520step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39521Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39521step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39521step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39522Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39522step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39522step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39523Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39523step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39523step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39524Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39524step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39524step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39525Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39525step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw39525step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw39525step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39526Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39526step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw39526step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39526step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39527Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39527step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw39527step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39527step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39528Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39528step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw39528step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw39528step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39529Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39529step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39529step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39530Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39530step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw39530step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39530step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39531Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39531step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39531step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39532Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39532step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39532step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39533Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39533step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39533step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39533step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39534Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39534step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39534step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39535Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39535step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw39535step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39536Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39536step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39537Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39537step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39538Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39538step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39539Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39539step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39539step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39540Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39540step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw39540step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39540step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39541Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39541step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39541step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39542Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39542step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39542step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39542step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39543Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39543step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39543step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39543step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39544Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39544step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39544step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39545Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39545step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39545step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39546Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39546step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw39546step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39546step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39546step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39547Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39547step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39547step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39547step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39547step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39548Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39548step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39548step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39548step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39548step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39549Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39549step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw39549step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39549step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39549step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39550Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39550step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39550step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39550step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39551Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39551step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39551step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39551step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39552Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39552step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39552step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39552step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39553Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39553step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39553step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39553step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39554Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39554step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39554step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39554step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39555Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39555step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39555step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39555step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39556Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39556step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39556step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39557Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39557step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39557step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39558Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw39558step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39558step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39559Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39560Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39560step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39560step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39561Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39561step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw39561step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39561step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39562Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39562step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39563Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39563step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39563step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39563step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39564Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39564step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39564step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39565Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39565step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39565step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39566Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39566step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39567Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39567step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw39567step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39567step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39567step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39568Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39568step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw39568step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw39568step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39569Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39569step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39569step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39569step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39570Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39570step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39570step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39570step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39571Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39571step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39571step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39572Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39572step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39572step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39572step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39573Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39573step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw39573step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39573step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39574Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39574step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39574step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39574step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39575Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39575step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39575step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39576Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39576step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39576step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39577Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39577step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39577step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39578step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw39578step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39578step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw39578step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39579step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw39579step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39579step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw39579step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39580step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39580step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39581step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw39581step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39582step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39582step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39583step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39583step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw39584step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw39584step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw39585step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39585step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw39586step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39586step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39586step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39587step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39587step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39587step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39588Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39588step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39588step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw39589Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw39589step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39589step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39590Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39590step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39590step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39591Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39591step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw39591step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39591step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39592Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39592step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39592step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39593Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39593step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39593step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39593step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39594Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39594step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39595Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39595step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39595step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw39595step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39595step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39596Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39596step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39596step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw39596step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39596step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39597Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39597step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39597step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39597step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39597step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39598Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39598step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39598step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39598step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39599Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39599step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39599step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39599step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39600Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39600step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39600step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39601Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39601step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39601step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39601step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39602Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39602step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39602step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39602step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39603Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39603step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39603step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39603step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39603step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39604Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39604step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39604step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39604step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39604step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39605Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39605step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39605step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39605step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39605step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39606Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39606step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39606step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39607Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39607step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39607step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw39607step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39607step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39608Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39608step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39608step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39608step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39608step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39609Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39609step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39609step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39609step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39610step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw39610step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw39610step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39611step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw39611step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw39611step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw39611step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39612step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw39612step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39612step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw39612step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39613step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39613step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw39614step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw39614step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39615step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw39615step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39615step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39616Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39616step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39616step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39617Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39617step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39617step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw39617step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39617step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39618Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39618step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39618step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39618step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39619Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39619step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39619step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39619step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39620Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39620step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw39620step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39620step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39620step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39621Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39621step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39621step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39621step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39622Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39622step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39622step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39623Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39623step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw39623step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39623step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39624Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39624step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw39624step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw39624step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw39624step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39625Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39625step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw39625step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39625step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39626step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw39626step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39626step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw39626step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw39627step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw39627step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw39627step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw39628step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw39628step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39628step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39629Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39629step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw39629step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw39629step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39629step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw39629step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39630Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39630step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw39630step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39630step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39630step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39630step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39631Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39631step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw39631step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39631step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39632Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39632step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39632step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39632step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39633Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39633step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39633step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39633step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39634Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39634step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw39634step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39634step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39635Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39635step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39635step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39635step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39636Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw39636step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39636step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39637Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39637step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw39637step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39637step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39637step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39638Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39638step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw39638step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39638step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39638step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39639Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39639step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw39639step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39639step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39639step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39640Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39640step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39640step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39640step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39641Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39641step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw39641step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw39641step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39641step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39642step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![2, -3, 1]]
def raw39642step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]
def raw39642step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39642step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw39642step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39643step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39643step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39643step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39643step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39644step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![2, -1, -1]]
def raw39644step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw39644step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39644step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39644step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39645step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39645step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39645step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39646step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39646step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39646step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39646step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw39646step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39647step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39647step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39647step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39648step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39648step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39648step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39649step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39649step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39649step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39650step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39650step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39650step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39651Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39651step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw39651step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39651step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39652Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw39652step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39652step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39653step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw39653step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39653step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw39653step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39653step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw39653step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39653step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw39653step5Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39654step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39654step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw39654step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39655step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39655step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39656step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39656step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39657Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39657step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39657step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39658Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39658step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39658step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39659Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39659step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39659step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39660Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39660step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39660step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39660step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39661Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39661step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39661step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw39661step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39662Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39662step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39662step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39663Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39663step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39664Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39664step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw39664step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39664step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39664step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39665Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39665step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39665step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39665step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39666Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39666step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39666step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39667Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39667step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39667step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39668Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39668step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39669Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39669step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39670Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39670step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39670step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39671Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39671step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39671step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39672Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39672step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39673Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39673step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39673step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39673step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39674Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39674step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39674step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39675Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39675step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39675step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39675step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39676Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39676step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39676step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39677Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39677step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39677step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39678Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39678step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39679Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39679step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw3971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3971step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3975step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw3975step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw3975step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw3975step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw3976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw3977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw3977step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw3977step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3980step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw3980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw3980step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3980step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw3980step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3981step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw3992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw3996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw4003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39680Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39680step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39680step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39680step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39681Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39681step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39681step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39681step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39682Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39682step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39682step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39683Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39683step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39683step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39684Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39684step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39684step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39684step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39685Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39685step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39685step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39685step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39685step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39686Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39686step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39686step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39686step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39687Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39687step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39687step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39687step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39688Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39688step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39688step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39689Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39689step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39689step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39689step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39690Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39690step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw39690step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw39690step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39690step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39691Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39691step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39691step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39691step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39692Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39692step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39692step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39692step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39693Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39693step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39693step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39693step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39693step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39694Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39694step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39694step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39695Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39695step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39695step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39695step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39696Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39696step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39696step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39697Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39697step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39697step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39698Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39698step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39699step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw39699step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39699step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw39699step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39700step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw39700step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39700step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39700step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39701step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39701step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39701step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39702step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39702step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw39702step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw39703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39703step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39703step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39704step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39704step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39704step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39705step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39705step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39706step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39706step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39707step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39707step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39708Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39708step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39708step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39709Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39709step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39709step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39710Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39710step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39710step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw39710step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw39710step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39710step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw39710step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39711Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39711step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39711step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39711step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39711step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39712Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39712step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39712step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39712step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39713Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39713step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39713step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39713step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39714Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39714step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39714step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39714step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39715Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39715step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39715step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39715step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39716Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39716step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39716step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39716step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39717Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39717step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39717step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39717step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39718Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39718step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39718step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39719Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39719step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39719step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39720Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39720step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39721step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39721step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39722Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39722step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39722step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39722step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39723Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39723step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw39723step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39723step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39724Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39724step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39724step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39725Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39725step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39725step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39725step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39726Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39726step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39726step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39727Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39727step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39728Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39728step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39729Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39729step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39730Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39730step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39731Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw39731step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39731step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39732Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39732step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39733Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39733step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39733step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39734Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39734step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39734step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39735Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39735step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39735step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39736Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39736step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39736step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39737Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39737step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39737step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39738Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39738step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39739Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39739step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39740Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39740step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39740step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39740step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39741Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39741step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39741step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39742Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39742step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39743Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39743step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39744Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39744step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39744step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39744step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39745Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39745step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw39745step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39745step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39746Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39746step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39746step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39746step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39747Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39747step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw39747step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39747step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39748Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39748step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39748step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39749Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39749step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39749step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39750Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39750step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39750step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39750step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39751Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39751step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw39751step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39751step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39752Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39752step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1]]
def raw39752step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw39752step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39752step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39752step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39753Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39753step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw39753step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39753step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39754Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw39754step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39754step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39754step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39755Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39755step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39755step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw39755step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39755step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39756Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39756step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39756step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39757Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39757step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39757step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39758Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw39758step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39758step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39759Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39759step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39759step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39759step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39760Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39760step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39760step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39761Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39761step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39761step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39762Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39762step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39762step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39762step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39763Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39763step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39763step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39764Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39764step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39764step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw39764step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw39764step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39764step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw39764step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39765Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39765step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39765step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39765step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39766Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39766step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw39766step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39766step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39766step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39766step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39767Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39767step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39767step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39768Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39768step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39768step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39769step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39769step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39769step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39769step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39770step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![1, -3, 2]]
def raw39770step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39770step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39770step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39771step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39771step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39772step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39772step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39773step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39773step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39774step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39774step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39775step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39775step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39775step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39776Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39776step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39776step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw39776step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39776step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39776step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39777Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39777step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39777step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39777step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39777step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39777step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39778Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39778step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39778step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39778step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39778step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39779Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39779step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39779step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw39779step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39780Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39780step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39780step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39780step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39781Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39781step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39781step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39781step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39782Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39782step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39782step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39782step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39783Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39783step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39783step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39783step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39784Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39784step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39784step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39785Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39785step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw39785step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39785step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39785step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39786Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39786step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39786step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39787Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39787step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39787step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39787step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39788Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39788step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39789Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39789step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39789step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39790Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39790step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39790step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39791Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39791step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39792Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39792step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39792step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39793Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39793step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39794Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39794step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39794step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39794step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39795Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39795step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39795step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39796Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39796step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39796step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39797Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39797step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39797step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39797step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39798Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39798step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39798step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39799Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39799step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39799step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39799step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39800Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39800step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39800step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39801Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39801step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39801step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39802Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39802step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39802step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39803Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39803step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39803step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39804Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39804step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw39804step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39804step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39804step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39805Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw39805step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39805step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39806Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39806step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39806step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39806step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39807Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39807step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39808Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39808step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39808step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39809Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39809step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39810Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39810step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39811Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39811step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39812Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39812step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39813Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39813step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39814Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39814step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39815step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39815step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39816step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39816step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39817step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39817step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39818step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39818step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw39819step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39819step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39820step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39820step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39821Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39821step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39822Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39822step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39823Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw39823step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw39823step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw39823step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39823step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39824Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw39824step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39824step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39824step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39825Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw39825step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39825step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39826Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw39826step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39826step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39827Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39827step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39828Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39828step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39829Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw39829step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39829step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39829step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39830Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39830step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39831Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39831step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39832Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39832step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39833Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw39833step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw39833step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39834Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39834step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39834step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39834step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39835Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39835step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39835step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39836Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw39836step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39836step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39837Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39837step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39838Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39838step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39839Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39839step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39840Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw39840step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39840step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39841Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw39841step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39841step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39842Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39842step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39843Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39843step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw39844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw39844step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw39844step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39846step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw39847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39847step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39848step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39850Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39850step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39850step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39851Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39851step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39851step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39852Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39852step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39852step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39853Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39853step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39854Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39854step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39854step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39855Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39855step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39855step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39856Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39856step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39856step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39857Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39857step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39857step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39857step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39858Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39858step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39858step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39859Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39859step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39860Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39860step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39861Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39861step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39861step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39862Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39862step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39862step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39863Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39863step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39863step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39864Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39864step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39864step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39865Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39865step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39866Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39866step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39867step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw39867step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39867step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39868step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39868step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39868step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw39869step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw39869step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39869step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39870step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39870step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39871Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39871step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39871step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39872Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39872step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39872step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39873Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw39873step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw39873step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw39873step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39874Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw39874step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39874step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39875step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw39875step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39875step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39876step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![2, -3, 1]]
def raw39876step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw39876step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39876step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39876step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39877step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![2, -2, 0]]
def raw39877step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39877step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39877step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw39878step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]
def raw39878step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39878step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw39879step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![2, 0, -2]]
def raw39879step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39879step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39880step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39880step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39880step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw39881step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39881step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39882step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39882step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39883step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39883step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw39884step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39884step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39885step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw39885step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw39885step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39886Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39886step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39887Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39887step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39888Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39888step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw39889Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw39889step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]
def raw39889step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39889step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw39890Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39890step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39890step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39890step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw39891Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39891step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39891step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw39892Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39892step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw39893Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39893step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw39894Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39894step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39894step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39895step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw39895step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39895step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39895step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39896step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw39896step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39896step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39896step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39897step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw39897step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39897step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw39898step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39898step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39898step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39899step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39899step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39899step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39900step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39900step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39900step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39901step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39901step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39902step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39902step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw39903step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39903step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39904step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39904step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw39905step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39905step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39906step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39906step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39906step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw39907step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw39907step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39907step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39908Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39908step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw39909Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39909step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw39910Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39910step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39910step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39911Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39911step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39911step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39912Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39912step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39912step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39912step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw39913Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw39913step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw39913step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39913step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39914Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39914step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw39915Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39915step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39916Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39916step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39916step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39917step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw39917step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39917step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw39918step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 2, -3], ![1, -3, 2]]
def raw39918step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39918step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw39919step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39919step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw39920step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39920step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw39921step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39921step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw39922step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39922step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw39923step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39923step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39923step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw39924step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw39924step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39924step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39925Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39925step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw39926step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![2, 2, -4]]
def raw39926step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39926step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw39926step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![2, 3, -5]]
def raw39927step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![2, 3, -5]]
def raw39927step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39927step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw39927step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw39928step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw39928step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39928step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39928step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![2, 3, -5]]
def raw39929step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39929step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 3, -4], ![1, -2, 1]]
def raw39930step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39930step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw39931step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39931step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 3, -4], ![1, -1, 0]]
def raw39932step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39932step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw39933step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39933step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39934step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw39934step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39934step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 3, -4], ![1, 0, -1]]
def raw39935step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw39935step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 2, -3], ![1, 1, -2]]
def raw39936step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw39936step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw39936step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw39937step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39937step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw39938step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39938step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw39939step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39939step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw39940step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39940step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw39941Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39941step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39942step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39942step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw39942step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39942step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39943step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39943step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39943step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39943step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39944step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw39944step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39944step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39945Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39945step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39945step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39945step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39946Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39946step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39946step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39946step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39947Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39947step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39947step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39948Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39948step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39948step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39949step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39949step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw39949step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39949step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39950step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39950step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39950step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39950step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39950step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39951step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw39951step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw39951step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39952step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39952step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39952step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39953step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw39953step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39953step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39954Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39954step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39954step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39955Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39955step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39955step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw39955step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39956Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39956step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39956step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39957Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39957step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39957step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39958Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39958step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39958step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39959step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw39959step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39960step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39960step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39961step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39961step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39962step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39962step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39963step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39963step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39964Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw39964step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39964step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39965Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw39965step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39965step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39966Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw39966step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39966step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39967Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39967step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39968Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39968step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39968step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39969Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39969step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39969step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39970Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39970step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39970step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39970step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39971Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39971step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39971step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39971step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw39972Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw39972step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39972step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39973Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39973step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39973step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39974Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39974step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39974step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39975Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39975step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39975step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw39976Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw39976step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39976step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39977Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39977step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw39977step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39977step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw39978Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw39978step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39978step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39979Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39979step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39980Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw39980step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw39981step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![2, -2, 0]]
def raw39981step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw39981step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw39982step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 2, -4]]
def raw39982step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw39982step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw39983step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39983step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39984Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw39984step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39984step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw39985step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw39985step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw39985step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39986step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw39986step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw39986step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39986step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39986step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw39987step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw39987step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39987step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39988step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw39988step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39988step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39989step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39989step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw39989step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39990step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw39990step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw39990step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw39991step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39991step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw39992step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39992step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39993step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw39993step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39994Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39994step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw39995Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw39995step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw39995step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw39995step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39995step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw39996Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw39996step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39996step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39996step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw39997Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39997step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw39997step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39997step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw39998step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw39998step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw39998step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw39999step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw39999step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw39999step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39999step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40000step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40000step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40000step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40000step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40001step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40001step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40001step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40002Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40002step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40002step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40003Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw40003step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw40003step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40003step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40004Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40004step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40004step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40005Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40005step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40005step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40006step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw40006step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40006step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40007step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40007step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40007step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw40008step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40008step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40008step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw40009step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]
def raw40009step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40009step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw40009step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw40010step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]
def raw40010step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40010step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw40010step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40011step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 2, -3], ![1, -1, 0]]
def raw40011step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40011step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40011step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw40012step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40012step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40013step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw40013step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw40014step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw40014step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw40014step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw40015step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40015step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw40016step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40016step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40017step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40017step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw40017step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40017step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40018Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40018step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40018step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40018step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40019step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40019step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw40019step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw40019step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40020Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40020step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40020step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40020step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40021step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw40021step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40022Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40022step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw40022step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40022step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40023Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw40023step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40023step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40024Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40024step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw40024step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40024step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40025Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40025step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40025step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40026step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40026step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw40026step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40027step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw40027step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40027step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40027step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40028step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40028step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40028step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40028step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40029step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40029step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40029step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40030Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40030step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40030step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40030step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40031Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40031step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40031step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40031step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40032Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40032step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40032step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40033step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40033step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw40033step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw40033step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40033step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw40033step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40034step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw40034step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40034step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40034step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40035step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw40035step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40035step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40035step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40035step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40036step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40036step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40036step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40037Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40037step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40037step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40038Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40038step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40038step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40038step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40039step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw40039step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw40039step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw40039step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40039step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw40039step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw40040step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]

end MUB6.Certificate.MixedSemantics

end OAI
end


