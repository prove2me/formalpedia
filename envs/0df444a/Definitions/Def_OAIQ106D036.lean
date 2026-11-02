-- Prove2me | Definitions.Def_OAIQ106D036
-- name    : OAIQ106D036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:20:08.139175+00:00
-- url     : https://prove2.me/theorems/9610afa6-9d79-4d15-a3e4-375cb379c96e
-- title:
--   Definitions bundle OAIQ106D036 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7650 declarations of OpenAI's Lean: 7650 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw42786step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42786step2`, `OAI.MUB6.Certificate.MixedSemantics.raw42786step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42786step3`, `OAI.MUB6.Certificate.MixedSemantics.raw42786step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42787`, `OAI.MUB6.Certificate.MixedSemantics.raw42787Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42787step0`, `OAI.MUB6.Certificate.MixedSemantics.raw42787step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42787step1`, `OAI.MUB6.Certificate.MixedSemantics.raw42787step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42788`, `OAI.MUB6.Certificate.MixedSemantics.raw42788Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step0`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step1`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step2`, `OAI.MUB6.Certificate.MixedSemantics.raw42788step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42789`, `OAI.MUB6.Certificate.MixedSemantics.raw42789Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42789step0`, `OAI.MUB6.Certificate.MixedSemantics.raw42789step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4278step0`, `OAI.MUB6.Certificate.MixedSemantics.raw4278step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw4279`, `OAI.MUB6.Certificate.MixedSemantics.raw42790`, `OAI.MUB6.Certificate.MixedSemantics.raw42790Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step0`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step1`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step2`, `OAI.MUB6.Certificate.MixedSemantics.raw42790step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42791`, `OAI.MUB6.Certificate.MixedSemantics.raw42791Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42791step0`, `OAI.MUB6.Certificate.MixedSemantics.raw42791step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw42792`, `OAI.MUB6.Certificate.MixedSemantics.raw42792Labels` and 7610 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical3.lean), [`MutuallyUnbiased_MixedSemantics_Canonical33`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical33.lean), [`MutuallyUnbiased_MixedSemantics_Canonical334`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical334.lean), [`MutuallyUnbiased_MixedSemantics_Canonical335`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical335.lean), [`MutuallyUnbiased_MixedSemantics_Canonical336`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical336.lean), [`MutuallyUnbiased_MixedSemantics_Canonical34`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical34.lean), [`MutuallyUnbiased_MixedSemantics_Canonical35`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical35.lean), [`MutuallyUnbiased_MixedSemantics_Canonical36`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical36.lean), [`MutuallyUnbiased_MixedSemantics_Canonical37`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical37.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound3184`, `OAI.MUB6.Certificate.MixedSemantics.sound3185`, `OAI.MUB6.Certificate.MixedSemantics.sound3190`, `OAI.MUB6.Certificate.MixedSemantics.sound3191`, `OAI.MUB6.Certificate.MixedSemantics.sound3203`, `OAI.MUB6.Certificate.MixedSemantics.sound3204`, `OAI.MUB6.Certificate.MixedSemantics.sound3205`, `OAI.MUB6.Certificate.MixedSemantics.sound3206`, `OAI.MUB6.Certificate.MixedSemantics.sound3207`, `OAI.MUB6.Certificate.MixedSemantics.sound3209`, `OAI.MUB6.Certificate.MixedSemantics.sound3210`, `OAI.MUB6.Certificate.MixedSemantics.sound3211`, `OAI.MUB6.Certificate.MixedSemantics.sound3223`, `OAI.MUB6.Certificate.MixedSemantics.sound3226`, `OAI.MUB6.Certificate.MixedSemantics.sound3227`, `OAI.MUB6.Certificate.MixedSemantics.sound3711`, `OAI.MUB6.Certificate.MixedSemantics.sound3726`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound100`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound116`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound129`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound153`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1785`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1847`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1859`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1866`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound188`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1972`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound236`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound269`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound296`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound35`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound93`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound98`, `OAI.MUB6.Certificate.MixedTargetSemantics.allKeyMoments`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound27`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound85`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound86`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound87`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound88`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound89` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1254`.
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

def raw42Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw42step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw42step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw42step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw43Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw43step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw43step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw44 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw44Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw44step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw44step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw44step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw44step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw45 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw45Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw45step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw45step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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

def raw430 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw431 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw431Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw431step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw432 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw433 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw433Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw433step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw436 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw436step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw437 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw437Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw437step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw438 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw439 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw439Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw439step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw439step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw440 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw441 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw441Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw441step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw443Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw443step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw450 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw451 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw451Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw451step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw453 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw453Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw453step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw454 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw455 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw455Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw455step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw456 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw457 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw457Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw457step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw458 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw459 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw459Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw459step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw461 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw461Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw461step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw462 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw463 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw463Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw463step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw464 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw465 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw465Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw465step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw470 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw471 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw471Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw471step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw471step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw472 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw472step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw473 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw473step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw474 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw474step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw475 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw475step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw475step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw477step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw478 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw479 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw479step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw481step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw481step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw483 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4281 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4282step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4282step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4282step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4283step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4283step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4283step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4283step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4284step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4284step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw4285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4285step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw4285step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4285step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4285step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4285step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4285step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4286step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw4286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4287step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4287step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4288step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4288step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4289step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4289step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4290step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4290step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4290step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4290step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4292step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4293step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4294step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4295step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4295step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4298step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4298step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4299step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4299step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4299step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4300step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4300step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw4302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4302step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4302step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4302step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4302step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw4307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4307step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw4307step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4307step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4307step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4307step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4307step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4308step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4308step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4308step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4308step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4309step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4309step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4309step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4309step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4310step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4310step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4310step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4310step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw4311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4311step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4311step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4311step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4311step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4311step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4311step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4313step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4314step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw4315step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4315step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw4315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4315step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4315step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4316step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw4316step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4316step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw4316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4316step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw4316step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4317step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4320step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4320step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4325step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4325step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4325step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw4329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw4330step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw4331step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4332step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw4332step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw4332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw4335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw4335step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw4336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4336step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw4337step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw4337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw4337step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![4, -3, -1]]
def raw4340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw4341step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4341step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4341step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4342 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4342step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4342step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4342step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4343step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4343step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4343step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4344step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4344step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4344step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4344step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4344step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4345step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4345step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4345step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4345step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4345step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4345step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4346step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4346step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4347step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4348step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4349step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4349step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4349step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4349step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4349step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4350step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4350step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4350step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4350step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4351step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical334
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42786step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42787Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42787step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42788Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42789Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42790Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42791Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42792Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42793Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42793step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42794Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42795Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42796Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42797Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42798Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42799Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42799step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw42799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42799step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42799step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42800Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42801Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42801step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42802Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42803Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42803step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42804Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42805Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw42805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42806Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42807Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42807step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42807step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42808Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42809Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42809step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42810Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42811Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42811step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42812Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-2, -2, 4]]
def raw42812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42812step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42812step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42813Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42813step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42813step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw42813step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42814Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42815Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42815step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw42815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42816Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42817Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42818Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42819Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42820Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42821Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42821step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42821step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw42821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42822Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42823Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42823step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw42823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42824Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42825Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42825step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42826Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42827Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42828Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42829Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42829step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42830Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42831Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42831step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw42831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42831step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42831step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42832Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42833Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw42835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42836Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42837Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42837step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw42837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42838Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42839Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42839step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42840Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42841Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42841step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw42841step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw42841step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42841step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw42841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42842Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42843Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw42843step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw42843step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42843step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw42843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42844Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42845Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42846Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42847Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42847step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw42847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42848Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42849Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42850Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42851Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw42851step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42852Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42853Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42853step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42854Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42855Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw42855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42856Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42857Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw42857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42858Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42858step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42858step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42859Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42859step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42859step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42860Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42861Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42861step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42862Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42863Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42863step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw42863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42863step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42863step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42864Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]
def raw42864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw42864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42865Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42865step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]
def raw42865step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42865step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42866Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42867Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42867step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42868Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42869Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42869step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42869step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42870Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42871Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42871step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42871step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42872Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42873Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42873step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42873step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42874Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42875Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42875step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42875step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42876Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42876step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42876step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42877Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42877step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42877step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42877step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42878Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42879Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42879step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42879step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42879step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical335
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42880Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42880step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42880step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42881Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42881step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42881step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42881step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42882Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42882step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw42882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42883Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42883step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw42883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42884Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw42884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42884step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42884step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42885Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42885step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw42885step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42885step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42886Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw42886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42886step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42886step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42887Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42887step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0]]
def raw42887step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42887step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42887step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42888Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1]]
def raw42888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42889Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1]]
def raw42889step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42889step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42890Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42890step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42891Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42891step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42891step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42892Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42893Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42893step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42893step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42894Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42895Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42895step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42896Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42896step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42897Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42898Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42899Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42899step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42899step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42899step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42900Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42901Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42902Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42902step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42902step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42903Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42903step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42903step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42903step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42904Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42904step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42904step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42905Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42905step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42905step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42905step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42905step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42906Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42907Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42907step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42907step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42908Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42909Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42909step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42910Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42911Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42911step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42911step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42912Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42913Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42915Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42915step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42917Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42917step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42918Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42918step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42919Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42919step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42919step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42920Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42921Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42921step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42921step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42922Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42923Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42923step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42924Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42925Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42925step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42926Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42926step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42926step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42927Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42927step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42928Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42928step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42929Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42930Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42930step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42931Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42931step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42931step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42931step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42932Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42933Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42933step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42933step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42934Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42935Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42935step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42936Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42936step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42936step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42936step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42937Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42937step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42937step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42938Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42939Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42939step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42940Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42941Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42941step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42942Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42943Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42944Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42945Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42945step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw42945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42946Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw42946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42947Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42947step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42948Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw42948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42949Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42949step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42950Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42950step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw42950step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42950step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42950step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42950step5 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42950step5Labels : Fin 2 → Fin 1 := ![0, 0]

def raw42951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42951Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42951step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42951step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw42951step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42951step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42951step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42951step5 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw42951step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw42952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42952Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42953Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42953step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42954Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42954step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw42954step1Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42954step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42954step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42954step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42954step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw42955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42955Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42955step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42955step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw42955step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw42955step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42955step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42955step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42955step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw42956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42956Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42957Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42957step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42957step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42958Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42959Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42959step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42960Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42961Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42961step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42961step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42961step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42962Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42963Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42963step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42964Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42965Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42965step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42965step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42966Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42967Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42967step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42967step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42968Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42969Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42969step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42970Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42970step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42971Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42972Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42972step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42973Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42973step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42973step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42973step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42974Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42975Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42975step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42975step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42975step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42975step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42975step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42976Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42977Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42978Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42978step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42979Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42979step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw42979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42980Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42981Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42981step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42981step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42982Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42983Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42984Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42985Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42985step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42986Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42987Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42987step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42987step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42988Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42989Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42989step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42990Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42991Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42991step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42992Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42993Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42993step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42994Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42995Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42995step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42996Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42997Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42997step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42998Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw42999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42999Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw43000Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw43000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw43001Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43002Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw43002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43003Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw43003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw43004Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw43005Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43005step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43005step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43006Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43007Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43007step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43007step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical336
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw43008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw43008Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw43009Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43010Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43011Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw43011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw43011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw43011step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw43011step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw43011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw43012Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw43012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw43013Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw43013step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw43014Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw43014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw43015Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw43015step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw43016Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw43017Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw43017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43019Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw43019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw43019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43020Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw43020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43020step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43021Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw43021step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw43021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43022Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43023Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43024Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43025Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43025step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw43026Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw43026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw43026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw43027Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw43027step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw43027step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43027step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw43028Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw43028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw43029Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw43030Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw43030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw43031Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw43031step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43031step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw43032Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw43032step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw43032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw43032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw43033Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw43033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw43034Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw43034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw43034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw43034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw43035Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43035step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw43035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw43036Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw43036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw43036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw43037Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw43037step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw43037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw43037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw43038Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw43038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw43038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw43039Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw43039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw43039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw43040Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw43040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw43040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw43041Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw43042Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw43042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw43042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw43043Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw43043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw43044Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw43044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw43044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw43045Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw43045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw43046Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw43046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw43046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw43046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw43047Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw43047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw43048Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw43048step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw43049Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43050Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw43050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43051Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw43051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw43052Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw43053Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw43054Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw43055Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw43056Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw43057Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw43058Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw43058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw43058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw43058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw43059Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43059step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw43060Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw43061Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw43062Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw43062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw43063Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw43063step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw43064Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw43064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw43065Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw43065step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw43066Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw43067Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw43067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43068Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43069Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43070Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw43070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw43070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw43070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43071Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw43071step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw43071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43072Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43073Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43074Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw43074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43075Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw43075step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43076Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43077Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43078Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw43078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw43078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw43078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43079Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43079step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43080Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43081Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43082Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw43083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43083Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43083step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4352step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4352step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4352step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4352step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4353step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4353step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4353step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4353step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4354step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4354step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4355step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw4356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw4356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4356step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4356step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4356step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4356step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4357 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4357step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4358 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4359 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4359step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4359step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4359step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw4359step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4360 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4360step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4360step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw4360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4361 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4361step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4364step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4364step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4366 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4367step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4367step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4367step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4368step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4368step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4368step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4369 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw4371step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw4371step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4371step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw4371step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, -1, 3]]
def raw4374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 1, -3], ![-2, -1, 3]]
def raw4374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4374step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -1, 3], ![2, 1, -3]]
def raw4374step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4375step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4375step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4376step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw4378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw4378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4378step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4378step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4379step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4379step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4380step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4380step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4382step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4382step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4382step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4382step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4383step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4383step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4383step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4383step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4383step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4384step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4384step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4385step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4386step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4387step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4387step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4387step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4388step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4388step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4389step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4389step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4389step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4389step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4390step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4390step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4391step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4391step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4391step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4391step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw4392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4392step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4392step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4392step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4392step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4393step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4393step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4393step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4394step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4394step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4394step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4394step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4395step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4395step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4395step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw4396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4396step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw4396step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4396step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4396step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4396step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4396step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4397step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4397step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4398step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4398step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4399step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4399step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4399step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4399step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]
def raw4400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4400step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw4400step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4400step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4400step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4400step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4400step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4402step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4403step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw4403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw4403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw4404step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4404step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw4404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4404step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw4404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4405step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4405step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4405step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw4405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4405step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw4405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4406step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4410step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4414step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4416step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw4416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw4418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw4419step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw4419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw4419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw4420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4421step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw4421step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4421step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw4421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4422step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4423step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4423step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4423step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw4425step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4425step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4425step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw4425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4426step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw4426step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4426step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw4426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4426step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw4426step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4427step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4428step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![4, -4, 0]]
def raw4429step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw4429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw4429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![4, -4, 0]]
def raw4430step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4430step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw4430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4430step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw4430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4431step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4432step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4433step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4433step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw4434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4434step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4434step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4435step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4435step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4435step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4435step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4436step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4439step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4440step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4440step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4441step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4441step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4444step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4445step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4446step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4447step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4449step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4449step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4450step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4451step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4451step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4451step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4451step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4452step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4454step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4455step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4455step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4455step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw4456step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4456step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4456step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4459step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4460step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4460step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4461step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4461step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4461step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4462step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4463step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4463step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw4463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4463step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw4463step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4464step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw4464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw4464step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4465step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4465step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4465step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw4465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4470step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4471step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4474step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4475step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4476step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4476step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4479step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4481step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4481step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw4484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4485step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4485step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4486step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4486step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4488step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4488step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4489step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4489step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4490step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4490step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4490step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4490step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw4490step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4491step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4491step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4491step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4491step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4491step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4492step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4492step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4493step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4493step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4493step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4493step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4494step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4494step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4494step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4494step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4494step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4495step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4495step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4495step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4495step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4495step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw4495step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4496step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4496step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4496step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4496step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4496step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4496step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4500step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4500step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4501step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4501step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4501step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4501step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4504step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4504step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4505step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4506step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw4506step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4506step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4506step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw4506step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4509step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4510step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw4510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4511step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4511step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw4511step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4511step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4511step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4511step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4511step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4512step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4512step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4513step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4513step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw4514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4515step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4515step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4515step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4515step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4515step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4516step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4516step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -3, 4], ![-2, 2, 0]]
def raw4516step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw4516step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4516step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw4516step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4518step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4519step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4520step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw4520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4520step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw4520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw4521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4521step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw4524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw4525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw4525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4525step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw4525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw4526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw4526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw4526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4527 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![3, -3]]
def raw4527step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw4527step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw4527step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4527step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw4527step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw4530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4531step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![4, -1, -3]]
def raw4532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-4, 3, 1]]
def raw4532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4532step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw4532step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![2, 1, -3]]
def raw4536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw4536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw4538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4540step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4541step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw4542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw4543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw4543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4543step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw4543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4544step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![3, 0, -3]]
def raw4545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw4546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw4546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4546step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw4546step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw4548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw4548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4551step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4552 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4554step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4559step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw4559step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4560 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4561 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4562step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4562step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw4562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4567step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4570step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw4570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4571step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4571step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4571step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4571step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4572step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4572step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4572step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4572step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4572step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4573step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw4573step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4573step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4573step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4573step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4574 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4574step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4574step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4574step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4574step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4574step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4575step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw4575step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4575step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw4575step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4575step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw4575step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4576 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4576step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4576step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4576step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4576step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4576step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4577Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4577step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4577step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4577step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4577step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4578step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4578step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4578step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4578step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4579step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4579step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4579step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4579step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4579step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4579step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4580step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4580step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4580step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4580step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4580step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4581 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4581step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4581step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4581step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4581step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4581step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4581step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4582Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4582step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4582step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4582step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4583Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4583step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4583step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4583step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4583step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4584step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4584step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4584step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4584step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4584step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4585step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4585step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4585step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4585step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4585step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4586step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4586step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4586step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4586step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4586step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4587Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4587step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4587step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4587step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4587step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4588step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4588step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4588step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4589step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4589step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4589step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4589step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4589step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4590step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4590step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4590step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4590step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-3, 0, 3]]
def raw4591step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4591step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw4591step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4591step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw4591step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4592step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4592step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4592step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4592step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4593step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4593step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4593step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4593step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4594 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw4594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4594step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4594step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4594step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-4, 1, 3]]
def raw4595step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw4595step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4595step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4595step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4595step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw4595step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw4596step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4596step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw4596step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4596step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4596step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4596step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4596step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4597step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4597step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4597step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4598step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4598step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4598step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4599step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4599step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4599step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4599step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4599step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4600step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4600step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4600step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4600step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4600step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4600step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4600step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-4, 1, 3]]
def raw4603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4603step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4603step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4607step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4608step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4610step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4614step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4614step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4616step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4616step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4616step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4621step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4621step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4621step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4623step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4623step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4624step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4624step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4624step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4624step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4625step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4625step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4625step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4625step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw4626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4662step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4671step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4672step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4672step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw4673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4680step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw4682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw4706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw4707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw4713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw4718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw4733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4736step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4737step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw4743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4744 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw4744step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw4744step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4744step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw4744step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw4749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw4753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4765step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4766 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4767step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4767step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4767step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4767step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4770step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4770step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4770step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4773step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4773step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4773step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4773step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4775 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4776 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4776step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4776step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw4776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4777 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw4780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4781 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4782 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4782step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4782step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw4782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4786step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4786step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw4786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4786step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw4786step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4790step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4791 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4794step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4794step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4794step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4796 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4796step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw4796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4796step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4796step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4799step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4799step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4799step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4799step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4799step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4800step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw4800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4800step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4800step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 0, 3]]
def raw4801step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4801step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw4801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4801step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw4801step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4802 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw4802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw4805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4805step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4805step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4805step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4805step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4805step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 0, 3]]
def raw4807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 0, 3]]
def raw4807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4807step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw4807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-4, 1, 3]]
def raw4808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw4813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw4814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![3, -1, -2]]
def raw4817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw4818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw4825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw4826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw4827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw4828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw4829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw4830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end


