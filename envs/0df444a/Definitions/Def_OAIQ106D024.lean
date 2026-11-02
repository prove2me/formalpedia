-- Prove2me | Definitions.Def_OAIQ106D024
-- name    : OAIQ106D024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:11:08.511023+00:00
-- url     : https://prove2.me/theorems/4fc95fad-45de-4638-8d52-4cf3bd17ea7b
-- title:
--   Definitions bundle OAIQ106D024 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7410 declarations of OpenAI's Lean: 7410 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw27476step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27476step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27477`, `OAI.MUB6.Certificate.MixedSemantics.raw27477Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step2`, `OAI.MUB6.Certificate.MixedSemantics.raw27477step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27478`, `OAI.MUB6.Certificate.MixedSemantics.raw27478Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27478step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27478step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27478step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27478step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27479`, `OAI.MUB6.Certificate.MixedSemantics.raw27479Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27479step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27479step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27479step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27479step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2747Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step3`, `OAI.MUB6.Certificate.MixedSemantics.raw2747step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2748`, `OAI.MUB6.Certificate.MixedSemantics.raw27480`, `OAI.MUB6.Certificate.MixedSemantics.raw27480Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27480step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27480step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27480step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27480step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27481`, `OAI.MUB6.Certificate.MixedSemantics.raw27481Labels` and 7370 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical21`, `MutuallyUnbiased_MixedSemantics_Canonical214`, `MutuallyUnbiased_MixedSemantics_Canonical215`, `MutuallyUnbiased_MixedSemantics_Canonical216`, `MutuallyUnbiased_MixedSemantics_Canonical217`, `MutuallyUnbiased_MixedSemantics_Canonical218`, `MutuallyUnbiased_MixedSemantics_Canonical219`, `MutuallyUnbiased_MixedSemantics_Canonical22`, `MutuallyUnbiased_MixedSemantics_Canonical220`, `MutuallyUnbiased_MixedSemantics_Canonical221`, `MutuallyUnbiased_MixedSemantics_Canonical222`, `MutuallyUnbiased_MixedSemantics_Canonical223`, `MutuallyUnbiased_MixedSemantics_Singletons45`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1165`, `OAI.MUB6.Certificate.MixedSemantics.sound1166`, `OAI.MUB6.Certificate.MixedSemantics.sound5296`, `OAI.MUB6.Certificate.MixedSemantics.sound5306`, `OAI.MUB6.Certificate.MixedSemantics.sound5310`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1780`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound101`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound117`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1657`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1674`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1685`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1816`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1909`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound198`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound268`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound349`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound372`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound572`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound621`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound8`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1074`.
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

def raw27Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw27step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw28 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]

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

def raw274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw274step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw274step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw275 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 3, -2]]
def raw275Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw275step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw275step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw275step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw275step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw276 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw277 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw277Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw277step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw278 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw278step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw279 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw279Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw279step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw280 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 3, -3]]
def raw280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw280step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw280step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw281 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 3, -3]]
def raw281Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw281step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw281step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw281step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw281step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw282 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw282step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw283 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw283Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw283step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw284 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw284step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw284step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw285 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 1, 1], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2747step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2747step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2747step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2748step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2748step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2748step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2749step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2749step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2749step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2750step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2750step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2750step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2754step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2754step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2754step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2754step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2755step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2757step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2757step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2757step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2758step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2758step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2758step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2759step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2759step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2760step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2760step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2760step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2777step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2777step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2777step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2777step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2778step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2778step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2779step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw2780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2780step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2780step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2780step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2781step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2781step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2802step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2806step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2807step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw2810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2811Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2811step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2811step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2812Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2812step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2812step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2813Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2813step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2813step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2814Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2814step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2815Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2815step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2815step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw27480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw27485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw27485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw27486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw27486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw27498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw27501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw27501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw27502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27503 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw27503Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![3, -3]]
def raw27503step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27503step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27503step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw27508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27517 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw27519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw27519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw27522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw27523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw27530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27539 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27539Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27539step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27539step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27539step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27539step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw27541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw27541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw27544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw27545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27546 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27546Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27546step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27546step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw27552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw27552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw27555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw27555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw27556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27557 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![3, -3]]
def raw27557Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![3, -3]]
def raw27557step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27557step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27557step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27565step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27565step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27565step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27565step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27567step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27567step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27567step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw27568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw27568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw27571step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27571step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27571step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw27571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw27572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw27580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27587step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw27590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27590step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27590step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27591step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27592step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27592step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27592step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw27593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw27593step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27593step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27593step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27593step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27594step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27594step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw27596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw27596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw27604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw27607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw27607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw27610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27610step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27610step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27614step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27616step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27617step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27617step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27617step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw27623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw27626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27638step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27639step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27640step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27641step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27641step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27642step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27642step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27642step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27642step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27643step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27643step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27644step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27644step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27644step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27645step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27645step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27646step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27646step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27646step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27646step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw27647step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27647step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27647step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27647step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical216
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27648step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27650step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27651step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27651step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27651step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27652step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27652step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27653step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27654step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27656step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27657step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27658step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27659step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27661step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27662step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27662step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27662step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw27663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27663step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw27664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27664step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27665step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27665step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27667step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27668step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27669step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27669step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27670step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27670step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27670step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27672step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27672step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27672step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27672step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27674step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27675step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27675step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27675step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27676step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27676step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw27685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw27687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27688step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27688step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27692step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27692step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw27696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27696step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27697step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27697step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27697step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27698step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27702step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27703step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27707step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw27707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27708step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw27712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27712step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27713step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27714step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27714step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27715step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw27717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27717step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27717step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27718step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27721step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27721step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27722step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw27728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw27733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw27733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27738step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw27738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw27738step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27738step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw27738step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27739step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw27739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw27739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw27741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw27742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw27742step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27743step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw27743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw27743step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27743step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw27743step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw27744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw27747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw27747step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27747step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27747step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw27752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw27753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27754 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw27754Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw27754step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27754step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27754step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27754step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27754step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw27755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw27756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw27757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw27758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27759step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27759step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27759step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27759step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27760 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27761 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27763step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27763step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27765 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27767 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27767step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27768step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27768step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27771 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27771step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27772 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27772step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27772step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27772step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27773 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27774 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw27775step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw27775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27776 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw27776step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27776step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27776step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27777 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27778 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -3, 1], ![-4, 1, 3]]
def raw27779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27780step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27781 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27781step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27781step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27781step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27781step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27781step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27782 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27783 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27784step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27784step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27784step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27784step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27785step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27785step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27785step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27785step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27786 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27786step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27787 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27787step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27787step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27789step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw27789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27789step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27789step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27789step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -2, 1], ![-4, 1, 3]]
def raw27790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27790step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27794 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27794step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27794step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27794step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27795step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27796 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27796step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw27800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27801 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27801step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27801step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27801step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27802step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw27802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27802step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27802step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27802step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27802step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw27805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -3, 1], ![-4, 1, 3]]
def raw27805step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27805step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27805step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27805step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27806 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27806step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27807 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27807step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27807step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27807step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27807step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27807step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27807step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27809step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27809step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27809step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27810 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27810step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27810step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27810step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27810step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27823 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw27823Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw27823step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27823step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27823step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw27823step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw27829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw27830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw27831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw27834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw27834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw27835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw27835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw27835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw27864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw27866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27867step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27871step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27872step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27873step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27874step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27875step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27879step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27882step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw27884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw27886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw27886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27892step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical218
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw27908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw27910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw27913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27914step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27916step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27917step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27917step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27919step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27919step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27920step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27921step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27922step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27922step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw27923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27925step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27925step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27925step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27927step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27927step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27927step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw27928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw27928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27928step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw27928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27929step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27930step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27930step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27930step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27931step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27931step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27931step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw27931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw27932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27932step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27933step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw27933step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw27933step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27933step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw27933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27934step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw27934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27934step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27934step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27935step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw27935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27935step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27935step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27935step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27937step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw27938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw27938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27938step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw27938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw27939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw27939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27939step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw27939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw27940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw27942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw27943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27950 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw27950Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw27950step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27950step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27950step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw27950step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27954 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw27954step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27954step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw27954step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27958step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27958step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw27958step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27962step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27962step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27962step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27967 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27967step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27967step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28000step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28001step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28001step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28002step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28002step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28003step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28003step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28004step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28004step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28004step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28005step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28006step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28006step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28006step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28007step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28007step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw28007step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28008step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28008step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28009step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28009step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28024step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28025step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28025step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw28028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28029step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28030step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical219
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28040step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw28045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw28045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw28050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw28052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28053step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw28053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw28054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw28075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw28079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw28080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw28080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw28082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw28082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28083step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28085step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw28085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw28085step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28085step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw28085step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28088step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw28090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw28090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw28090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw28095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw28095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28095step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw28095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28098step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28098step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw28100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw28100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw28100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw28105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw28105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw28105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28109step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28116 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw28116Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw28116step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28116step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw28116step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw28116step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28125 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28125step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28125step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28125step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28125step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28126 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28126step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28126step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28126step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28127 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw28128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28128step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28129step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28131step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28132 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28132step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28135step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28135step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28136 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw28136step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28136step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28137 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2816Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2816step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2816step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2817 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw2817Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2817step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]
def raw2817step0Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2817step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw2817step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2818step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2821step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2821step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2821step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2823step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2823step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2824step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2824step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2824step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2]]
def raw2825step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1]]
def raw2825step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2825step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1]]
def raw2825step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2826step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2826step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2826step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2827step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2828step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2829step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2832step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2833step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2833step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2834step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2834step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2834step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2835step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2835step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2836step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2836step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2836step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2836step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2837step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2837step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2837step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2839step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2840step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2841step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2842step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2843step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2843step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2843step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2843step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2843step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2844step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2844step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2846step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2848step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2848step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2849step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2850 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850step0Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![-2, 2]]
def raw2850step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]
def raw2850step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2850step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2852step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2854step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2854step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2854step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2854step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical220
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw28168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw28169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw28169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw28172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw28172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw28173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw28173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28174 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw28174Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw28174step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28174step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw28174step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw28201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw28213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw28216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28218 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw28218Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![-1, 1], ![3, -3]]
def raw28218step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28218step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28218step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw28226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![4, -3, -1]]
def raw28231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw28231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28232 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw28232Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]
def raw28232step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw28232step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw28232step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw28277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28280step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw28285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw28285step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw28286step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28286step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw28286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28287step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical221
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28296step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28299step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28300step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28301step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28301step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw28302step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw28302step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28303step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![4, -2, -2]]
def raw28306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28306step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28306step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28310step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28310step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28310step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28311step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28311step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28311step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28312step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28312step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28312step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28312step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw28314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28315step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw28315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28315step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw28315step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28315step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw28315step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28316step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw28316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28316step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw28316step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28316step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw28316step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw28317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28318step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28320step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28321step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw28321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28321step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28321step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw28322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28322step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw28326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw28326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28327step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw28327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28327step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28327step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28327step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![3, -1, -2]]
def raw28328step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28328step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28331step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw28331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw28331step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28331step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw28331step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28332step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-2, -2, 4]]
def raw28332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw28332step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw28332step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![4, -2, -2]]
def raw28333step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw28335step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw28336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![4, -2, -2]]
def raw28336step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw28337step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28337step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28337step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28337step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28338step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28338step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28338step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28338step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28339step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28339step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28340step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28340step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28340step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28340step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28341step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28342step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28342step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28342step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28342step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28343step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28343step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw28344step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28344step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28344step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw28344step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28346step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28346step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28346step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28347step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28347step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28348step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28348step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28350step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28350step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28351step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28351step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw28353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28353step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28356step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28356step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28356step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28356step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28356step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28357step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28357step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -3, 0]]
def raw28358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw28359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw28359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw28359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw28360step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28360step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw28360step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28360step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw28360step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw28361step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28361step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28361step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw28361step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![4, -4, 0]]
def raw28363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28363step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28363step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![4, -4, 0]]
def raw28364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28364step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28364step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28364step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28364step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw28395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw28398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw28398step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28398step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28399step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28400step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28400step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw28403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw28403step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28403step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw28403step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28404step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28405step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28405step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28408step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28409step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28410step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28413step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28413step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28414step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28415step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28415step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical222
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28416step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw28419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28419step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28419step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw28420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28420step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28421step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![4, -1, -3]]
def raw28424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw28424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw28424step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28424step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw28424step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]
def raw28428step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28428step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28428step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw28428step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28429step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw28430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw28430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw28430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![3, 0, -3]]
def raw28433step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28433step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw28433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28433step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw28433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw28434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw28435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28438step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28438step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw28440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw28440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw28444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw28445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw28445step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28445step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw28445step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw28446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw28449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw28449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28449step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw28450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw28450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28451step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw28451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw28453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw28454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![4, -1, -3]]
def raw28454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![4, -1, -3]]
def raw28454step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28454step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw28454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28454step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw28454step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw28455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw28455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![3, 0, -3]]
def raw28459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw28460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![4, -1, -3]]
def raw28460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw28460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28461 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw28461Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![3, -3]]
def raw28461step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![3, -3]]
def raw28461step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw28461step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw28461step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28461step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw28461step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw28464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw28464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28464step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw28494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw28494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw28498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw28499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw28512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw28512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28515step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw28516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw28525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw28529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw28530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw28531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw28532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw28533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw28534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw28535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28536 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw28536Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw28536step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw28536step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw28536step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28536step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw28536step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw28542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28543 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28543Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28543step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28543step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28543step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28543step2Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical223
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28550 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw28550Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28550step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw28550step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28550step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw28550step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Singletons45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def singletonSmall2903 : Fin 2 → Fin 1 := ![0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


