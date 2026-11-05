-- Prove2me | Definitions.Def_OAIQ106E110
-- name    : OAIQ106E110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:20:00.863757+00:00
-- url     : https://prove2.me/theorems/3f602be0-47cd-4d5b-aefa-5d0432c73d4b
-- title:
--   Definitions bundle OAIQ106E110 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7530 declarations of OpenAI's Lean: 7530 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw37074step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37074step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37074step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37074step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37074step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37074step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37075`, `OAI.MUB6.Certificate.MixedSemantics.raw37075Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37075step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37076`, `OAI.MUB6.Certificate.MixedSemantics.raw37076Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37076step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37077`, `OAI.MUB6.Certificate.MixedSemantics.raw37077Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37077step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37078`, `OAI.MUB6.Certificate.MixedSemantics.raw37078Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step0`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step1`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step2`, `OAI.MUB6.Certificate.MixedSemantics.raw37078step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw37079`, `OAI.MUB6.Certificate.MixedSemantics.raw37079Labels` and 7490 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical28`, `MutuallyUnbiased_MixedSemantics_Canonical289`, `MutuallyUnbiased_MixedSemantics_Canonical29`, `MutuallyUnbiased_MixedSemantics_Canonical290`, `MutuallyUnbiased_MixedSemantics_Canonical291`, `MutuallyUnbiased_MixedSemantics_Canonical292`, `MutuallyUnbiased_MixedSemantics_Canonical293`, `MutuallyUnbiased_MixedSemantics_Canonical294`, `MutuallyUnbiased_MixedSemantics_Canonical295`, `MutuallyUnbiased_MixedSemantics_Canonical297`, `MutuallyUnbiased_MixedSemantics_Canonical298`, `MutuallyUnbiased_MixedSemantics_Canonical3`, `MutuallyUnbiased_MixedSemantics_Canonical30`, `MutuallyUnbiased_MixedSemantics_Canonical308`, `MutuallyUnbiased_MixedSemantics_Canonical309`, `MutuallyUnbiased_MixedSemantics_Canonical31`, `MutuallyUnbiased_MixedSemantics_Canonical310`, `MutuallyUnbiased_MixedSemantics_Canonical311`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1172_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3094_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3100_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3106_e`, `OAI.MUB6.Certificate.MixedSemantics.sound3109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound132_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound133_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound134_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound135_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1785_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero488_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1423_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound244_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound504_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound540_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound635_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound657_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound700_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound711_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound722_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound790_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound0_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound10_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound11_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound1_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound23_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound4_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound6_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound7_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`.
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

def raw370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw371Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw371step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw372 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw3708step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3708step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-3, 3, 0]]
def raw3708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3708step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw3708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical289
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37077step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw37079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37083step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw37094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw37095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw37099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37102step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37103step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw3713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw3713step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3713step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw3714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw3714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw3718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3718step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw3718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw3719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3721 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]

def raw3721step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-3, 3]]
def raw3721step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-3, 3]]
def raw3721step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -3], ![-3, 3]]
def raw3721step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3721step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw3721step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw3723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-2, 2, 0], ![-2, 2, 0]]
def raw3724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3724step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw3725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -3, 3], ![-1, 1, 0], ![-3, 3, 0]]
def raw3725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def raw3725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw3726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw3726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw3726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw3728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw3729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw3730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw3732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def raw3732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0], ![-3, 0, 3]]
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical290
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37128step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37129step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37130step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37132step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37133step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37134step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw37135step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37138step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37139step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37140step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37143step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37144step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37145step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37148step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37149step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37153step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37154step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37155step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw37161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw37181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw37208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37210step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37213step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37214step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37232step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37232step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37233step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37234step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37235step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw37235step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37235step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37235step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37236step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37236step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37236step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37237step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37237step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37237step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37238step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37238step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37238step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37239step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw37239step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37239step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37239step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37240step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37240step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37240step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37241step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37241step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37241step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37242step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw37242step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37242step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37242step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw37243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37243step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw37248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw37249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw37250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37252step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37252step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37253step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw37260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw37262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw37263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37263step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw37265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw37278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw37281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw37284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw37291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw37293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37300step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37301step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37303step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw37306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw37306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw37308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37309step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw37312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw37313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw37313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw37317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw37318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw37318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw37321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw37322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw37323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37324step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37324step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37325step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw37325step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37325step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37325step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37326step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw37326step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37326step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37326step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37326step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37327step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37327step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37327step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37328step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37328step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37328step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37328step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37328step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw37329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37329step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw37329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37329step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw37329step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37330 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-3, -2, 5]]
def raw37330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 2, -5], ![-3, -2, 5]]
def raw37330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37330step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw37330step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37331step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw37332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -2, 5]]
def raw37333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37333step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-3, -2, 5]]
def raw37333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

end MUB6.Certificate.MixedSemantics

end OAI
end


