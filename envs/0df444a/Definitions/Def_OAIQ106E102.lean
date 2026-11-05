-- Prove2me | Definitions.Def_OAIQ106E102
-- name    : OAIQ106E102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:12:55.130201+00:00
-- url     : https://prove2.me/theorems/62a04556-c419-4a0e-81a8-b22d6096e778
-- title:
--   Definitions bundle OAIQ106E102 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7455 declarations of OpenAI's Lean: 7455 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw26750`, `OAI.MUB6.Certificate.MixedSemantics.raw26750Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26750step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26750step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26751`, `OAI.MUB6.Certificate.MixedSemantics.raw26751Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26751step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26751step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26751step1`, `OAI.MUB6.Certificate.MixedSemantics.raw26751step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26752`, `OAI.MUB6.Certificate.MixedSemantics.raw26752Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26752step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26752step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26753`, `OAI.MUB6.Certificate.MixedSemantics.raw26753Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26753step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26753step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26754`, `OAI.MUB6.Certificate.MixedSemantics.raw26754Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26754step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26754step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26755`, `OAI.MUB6.Certificate.MixedSemantics.raw26755Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26755step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26755step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26756`, `OAI.MUB6.Certificate.MixedSemantics.raw26756Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26756step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26756step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26756step1`, `OAI.MUB6.Certificate.MixedSemantics.raw26756step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26757`, `OAI.MUB6.Certificate.MixedSemantics.raw26757Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26757step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26757step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26758`, `OAI.MUB6.Certificate.MixedSemantics.raw26758Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw26758step0`, `OAI.MUB6.Certificate.MixedSemantics.raw26758step0Labels` and 7415 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical2`, `MutuallyUnbiased_MixedSemantics_Canonical20`, `MutuallyUnbiased_MixedSemantics_Canonical208`, `MutuallyUnbiased_MixedSemantics_Canonical209`, `MutuallyUnbiased_MixedSemantics_Canonical21`, `MutuallyUnbiased_MixedSemantics_Canonical210`, `MutuallyUnbiased_MixedSemantics_Canonical211`, `MutuallyUnbiased_MixedSemantics_Canonical212`, `MutuallyUnbiased_MixedSemantics_Canonical213`, `MutuallyUnbiased_MixedSemantics_Canonical214`, `MutuallyUnbiased_MixedSemantics_Canonical215`, `MutuallyUnbiased_MixedSemantics_Canonical216`, `MutuallyUnbiased_MixedSemantics_Canonical217`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1165_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2766_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound100_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound104_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound112_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound122_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1674_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero621_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1159_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1178_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound138_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound140_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound141_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1517_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1651_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1662_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound16_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1739_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1911_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2037_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2046_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2048_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2049_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2062_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2077_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2105_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound255_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound286_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound498_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound532_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound543_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound548_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound558_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound571_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound613_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound631_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound633_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound659_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound667_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound675_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound718_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound792_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound7_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound899_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound94_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`.
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

def raw26Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw26step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw26step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]

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

def raw267Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw267step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw267step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw268 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw269 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw269Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw269step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw270 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw270step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw271 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw271Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw271step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw271step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw272 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw273 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw273Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw273step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw274 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 3, -2]]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2679step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2679step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2684step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2684step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2684step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw2686step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2686step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2686step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2686step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2687step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical208
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical209
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26762step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26763step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26765step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26765step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26765step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26767step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26771step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26771step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26777step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26777step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26781step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw26782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw26783step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26783step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26784step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw26785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26785step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw26796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26804step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26806step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26807step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26808step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26809step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26810step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26811step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26812step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26813step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26814step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26815step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw26816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26816step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26817step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26818step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26819step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26820step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw26821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26821step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw26840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw26841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw26845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw26846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw26851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26857step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26858 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26858step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw2688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2688step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2688step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2688step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2689step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2689step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2689step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2689step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2690step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2690step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2690step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw2706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw2711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw2716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2719step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2723step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2723step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2723step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2723step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2723step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2724step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2724step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2724step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2724step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2724step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw2726step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2726step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2726step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2728step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2729step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw2731step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2731step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2733step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2733step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2734step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2734step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2734step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2736step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2736step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2736step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2736step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2737step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2737step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2738step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2738step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2741step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2741step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2741step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2742step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2742step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2742step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2743step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2744step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2746step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2746step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2746step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2746step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical210
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw26882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw26883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26884 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1], ![0, 0]]
def raw26884Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26884step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw26884step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26884step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw26884step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw26889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw26890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26891 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26891Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![0, 0], ![-1, 1]]
def raw26908Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw26908step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26908step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26908step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw26911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw26912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw26912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw26913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw26913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw26914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![0, 0], ![-1, 1]]
def raw26915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![-1, 1]]
def raw26915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw26918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw26919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26921 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw26921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26922 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26923 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw26923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw26924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw26925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw26932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw26941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw26942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw26945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw26952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26954step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26954step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw26956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26957step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw26961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw26961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw26962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw26964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw26964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw26965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw26965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw26969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw26970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw26971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26977step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26978step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26984step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26985step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26987step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26989step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw26990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw26991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26991step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw26993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw26998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw26999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical211
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw27011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27012 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27012step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27013step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27014 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27014step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27015 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27015step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27016step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27016step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27016step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27017step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27019step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27020step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27021step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27021step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27021step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27022step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27023step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27024step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27025step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27026step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27026step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27027step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27028step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27029step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27030step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27031 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27031step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27031step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27032step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27033step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw27034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27034step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27035 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27035step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27035step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27036step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27037step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27038step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw27039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27039step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw27044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw27044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw27044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw27045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw27045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27046 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![1, -1], ![0, 0], ![-1, 1]]
def raw27046Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![1, -1], ![-1, 1]]
def raw27046step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![1, -1], ![-1, 1]]
def raw27046step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27046step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw27049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw27050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1]]
def raw27051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw27051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw27051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1]]
def raw27052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1]]
def raw27052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27053 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![2, -2], ![0, 0], ![-1, 1]]
def raw27053Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![2, -2], ![-1, 1]]
def raw27053step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw27053step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27053step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw27058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw27058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw27059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw27059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27060 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw27060Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27060step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw27060step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27060step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27060step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27062step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27063step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27063step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27063step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27064step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27064step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27064step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27064step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27065step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27065step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27065step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw27078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27080step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw27085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw27090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27094step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27094step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27094step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27094step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27095step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27095step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27095step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27095step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27098step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27101step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw27103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw27103step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw27103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27104step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27104step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27104step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27104step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27105step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27105step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27105step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27108step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27108step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27108step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27109step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27109step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27109step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27110step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27110step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27110step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27110step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27110step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27111step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw27115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27115step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27115step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27115step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27115step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27115step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27116step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw27120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27120step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27120step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27120step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27120step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27120step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical212
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27175step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27175step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27175step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27175step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw27195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw27205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw27206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27207 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1], ![0, 0], ![0, 0]]
def raw27207Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1], ![0, 0]]
def raw27207step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw27207step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27207step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27207step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw27211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0]]
def raw27212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw27212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0]]
def raw27213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw27213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27214 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2], ![0, 0], ![0, 0]]
def raw27214Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27214step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2], ![0, 0]]
def raw27214step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27214step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27214step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27215step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27215step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27215step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27215step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27216step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27217step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27218step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27219step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27219step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw27233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw27234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw27239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw27244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27263step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27263step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27263step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27264step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27264step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27265step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27265step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27266step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27272step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27272step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27272step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27272step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw27287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27293step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27293step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27294step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27294step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27295step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27295step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27296step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27296step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27297step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw27297step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27297step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27297step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27298step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw27298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27298step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27298step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27299step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27299step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27299step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27300step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27300step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27300step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27301step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27301step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27302step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw27302step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27302step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27303step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw27303step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27303step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw27304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27304step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27304step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw27305step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27305step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27305step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27306step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw27306step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27306step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27306step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27307step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw27307step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27307step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27307step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw27308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw27308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw27308step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27308step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw27312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw27314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw27317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw27317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27319 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw27319Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-1, 1], ![-3, 3]]
def raw27319step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-3, 3]]
def raw27319step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27319step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw27326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw27326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw27326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27333 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27333step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27333step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27340 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27342 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw27342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw27347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw27353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw27353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw27354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw27354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27355 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27355step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27360 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27361 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27362 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw27362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw27362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw27363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw27363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw27366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27367 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27378 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw27389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw27389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw27392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27394 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw27394Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw27394step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27394step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27394step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw27403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw27403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27409 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27409step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27409step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27410 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27413 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw27414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw27415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw27417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw27418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw27418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw27419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw27419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw27420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27424 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw27424step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27424step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw27425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw27425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![3, -1, -2]]
def raw27426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw27426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw27426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw27427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw27428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![3, -1, -2]]
def raw27429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw27429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw27429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw27430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw27430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![4, -2, -2]]
def raw27430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw27430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw27430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27431 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw27431Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw27431step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]
def raw27431step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw27431step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw27434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw27435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw27439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27453 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27466 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw27466Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw27466step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw27466step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27466step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw27470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw27475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw27476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw27819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


