-- Prove2me | Definitions.Def_OAIQ106E099
-- name    : OAIQ106E099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:09:09.70349+00:00
-- url     : https://prove2.me/theorems/d0ba30b9-8e00-4804-8fa8-2f02ccb6d560
-- title:
--   Definitions bundle OAIQ106E099 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2785 declarations of OpenAI's Lean: 2785 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw23174step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23174step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23174step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23175`, `OAI.MUB6.Certificate.MixedSemantics.raw23175Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23175step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23175step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23175step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23175step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23176`, `OAI.MUB6.Certificate.MixedSemantics.raw23176Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23176step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23176step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23177`, `OAI.MUB6.Certificate.MixedSemantics.raw23177Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23177step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23177step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23177step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23177step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23178`, `OAI.MUB6.Certificate.MixedSemantics.raw23178Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23178step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23178step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23178step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23178step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23179`, `OAI.MUB6.Certificate.MixedSemantics.raw23179Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23179step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23179step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23179step1`, `OAI.MUB6.Certificate.MixedSemantics.raw23179step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2317Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2317step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2317step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2318`, `OAI.MUB6.Certificate.MixedSemantics.raw23180`, `OAI.MUB6.Certificate.MixedSemantics.raw23180Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23180step0`, `OAI.MUB6.Certificate.MixedSemantics.raw23180step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw23181` and 2745 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical18.lean), [`MutuallyUnbiased_MixedSemantics_Canonical181`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical181.lean), [`MutuallyUnbiased_MixedSemantics_Canonical182`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical182.lean), [`MutuallyUnbiased_MixedSemantics_Canonical183`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical183.lean), [`MutuallyUnbiased_MixedSemantics_Canonical184`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical184.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2594_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound68_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound83_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1796_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1925_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound643_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`.
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

def raw231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw231step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw232 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw233 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw233step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw234 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw235 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw235step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw236 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2317step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2318 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2318Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2318step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2319 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2319step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2319step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2320 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2320step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2321 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![1, 2, -3]]
def raw2321Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2321step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2321step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw2321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2322 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2322step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2323 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2323step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2324 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2324Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2324step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2325 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2325step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2325step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2326 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2326step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2327 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 1, -2], ![-2, 2, 0]]
def raw2327Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2327step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw2327step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2327step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw2327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2357Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2358 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2359 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw2359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw2359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2360 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -2, 2], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]

def raw23174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23182step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw23183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw23185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23186step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw23187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23187step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23188step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23188step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23188step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw23190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23191step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23191step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23191step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23191step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23196step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw23197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw23197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw23198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw23201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23201step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw23201step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw23203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw23203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23204step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw23204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23204step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw23204step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23226step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw23238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23238step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw23242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw23256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23260 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23265 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23270step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23271step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23274 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw23276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23277step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23278 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23284step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23285 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23289step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23289step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23290step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23295step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23304step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23314 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw23314Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw23314step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw23314step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw23314step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23329step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23336step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23352step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw23356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23364step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw23364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23380step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw23380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23384step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw23384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23385step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw23385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw23392step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw23392step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23393step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23409step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw23409step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23413step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw23413step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23414step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw23414step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw23418step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw23418step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical183
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-3, 1, 2]]
def raw23477step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23530step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw23534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 0, -2], ![1, 0, -1]]
def raw23538step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23538step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23538step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23538step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23551step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw23551step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical184
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23552step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23552step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23553step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23553step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23554step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw23554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23554step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw23554step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23555step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23555step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23555step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw23555step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23555step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw23555step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw23556step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw23556step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw23556step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23556step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw23556step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw23557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23557step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw23557step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23561step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw23562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23562step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw23562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -2, 2], ![0, -2, 2]]
def raw23568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23568step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw23568step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw23568step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw23568step5Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw23573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw23574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23581step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw23581step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw23581step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23582step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23582step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23582step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw23583step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23583step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23583step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw23596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw23598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw23602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23602step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw23603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw23607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw23608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


