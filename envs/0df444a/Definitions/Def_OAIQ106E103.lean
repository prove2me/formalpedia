-- Prove2me | Definitions.Def_OAIQ106E103
-- name    : OAIQ106E103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:12:20.537742+00:00
-- url     : https://prove2.me/theorems/c6709950-d92e-4e47-abee-b0a47f24c272
-- title:
--   Definitions bundle OAIQ106E103 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7510 declarations of OpenAI's Lean: 7510 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw27819step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2781Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step0`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step1`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step2`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step3`, `OAI.MUB6.Certificate.MixedSemantics.raw2781step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw2782`, `OAI.MUB6.Certificate.MixedSemantics.raw27820`, `OAI.MUB6.Certificate.MixedSemantics.raw27820Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step2`, `OAI.MUB6.Certificate.MixedSemantics.raw27820step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27821`, `OAI.MUB6.Certificate.MixedSemantics.raw27821Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step2`, `OAI.MUB6.Certificate.MixedSemantics.raw27821step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27822`, `OAI.MUB6.Certificate.MixedSemantics.raw27822Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step1`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step2`, `OAI.MUB6.Certificate.MixedSemantics.raw27822step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27823`, `OAI.MUB6.Certificate.MixedSemantics.raw27823Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27823step0`, `OAI.MUB6.Certificate.MixedSemantics.raw27823step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw27823step1` and 7470 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical21`, `MutuallyUnbiased_MixedSemantics_Canonical217`, `MutuallyUnbiased_MixedSemantics_Canonical218`, `MutuallyUnbiased_MixedSemantics_Canonical219`, `MutuallyUnbiased_MixedSemantics_Canonical22`, `MutuallyUnbiased_MixedSemantics_Canonical220`, `MutuallyUnbiased_MixedSemantics_Canonical221`, `MutuallyUnbiased_MixedSemantics_Canonical222`, `MutuallyUnbiased_MixedSemantics_Canonical223`, `MutuallyUnbiased_MixedSemantics_Canonical224`, `MutuallyUnbiased_MixedSemantics_Canonical225`, `MutuallyUnbiased_MixedSemantics_Canonical226`, `MutuallyUnbiased_MixedSemantics_Canonical227`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2828_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound106_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound35_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound10_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1318_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1669_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1874_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1906_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1907_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2040_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2076_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound207_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound547_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound585_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound600_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound6_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound736_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound741_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound743_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`.
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
def raw28Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw28step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]

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
def raw285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw285step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw285step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw286 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw287 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw287Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw287step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw288 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw289 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw289Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw289step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical217
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]

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
def raw2855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw2855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2855step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2856step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw2871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2871step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2872step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw2876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw2876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2876step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2880step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw2880step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2881step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2882step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2884step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2884step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2885step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2894step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2899step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]
def raw2901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]
def raw2901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]
def raw2901step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2902step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2903step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2904step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2907step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]

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
def raw28551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw28554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw28557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw28558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw28559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw28559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw28560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28561 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![0, 0], ![3, -3]]
def raw28561Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw28561step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw28561step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28561step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw28561step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw28575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw28585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw28587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw28588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28591step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw28591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28598step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28598step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw28598step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw28600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw28613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![4, -1, -3]]
def raw28614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28615step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28615step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28616step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28617step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28617step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw28618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28622step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28625step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28626step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28629step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28629step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28629step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28630step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28631step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28633step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28635step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw28636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw28640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw28640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw28640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw28641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw28641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw28649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw28650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw28651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28654step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28654step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 1, -2], ![4, -4, 0]]
def raw28655step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28655step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![4, -4, 0]]
def raw28657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -4, 0]]
def raw28658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![4, -4, 0]]
def raw28658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw28658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw28658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical224
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28679step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw28733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw28767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw28780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw28780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical225
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28815step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28827step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28834step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw28835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw28836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw28837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw28837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw28838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw28838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw28848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw28848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28851step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28851step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28855step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28861step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28886step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28886step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28887step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28888step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28892step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28894step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28895step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28895step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28898step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw28899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28899step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28900step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28902step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw28903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw28904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28904step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw28913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw28913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical226
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw28988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29011 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29011Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw29011step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29011step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29011step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29032 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw29032Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29032step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29032step0Labels : Fin 2 → Fin 2 := ![0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical227
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29066step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29066step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step6Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw29071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29071step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


