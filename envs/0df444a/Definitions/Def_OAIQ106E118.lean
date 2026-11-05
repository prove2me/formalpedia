-- Prove2me | Definitions.Def_OAIQ106E118
-- name    : OAIQ106E118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:26:46.493376+00:00
-- url     : https://prove2.me/theorems/fa140e9f-6b20-4609-abd1-da0434c671ce
-- title:
--   Definitions bundle OAIQ106E118 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7565 declarations of OpenAI's Lean: 7565 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw8502`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step0`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step1`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step2`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step3`, `OAI.MUB6.Certificate.MixedSemantics.raw8502step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8503`, `OAI.MUB6.Certificate.MixedSemantics.raw8503Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step0`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step1`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step2`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step3`, `OAI.MUB6.Certificate.MixedSemantics.raw8503step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8504`, `OAI.MUB6.Certificate.MixedSemantics.raw8504Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step0`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step1`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step2`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step3`, `OAI.MUB6.Certificate.MixedSemantics.raw8504step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8505`, `OAI.MUB6.Certificate.MixedSemantics.raw8505Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step0`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step1`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step2`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step3`, `OAI.MUB6.Certificate.MixedSemantics.raw8505step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw8506` and 7525 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical6`, `MutuallyUnbiased_MixedSemantics_Canonical66`, `MutuallyUnbiased_MixedSemantics_Canonical67`, `MutuallyUnbiased_MixedSemantics_Canonical68`, `MutuallyUnbiased_MixedSemantics_Canonical69`, `MutuallyUnbiased_MixedSemantics_Canonical7`, `MutuallyUnbiased_MixedSemantics_Canonical70`, `MutuallyUnbiased_MixedSemantics_Canonical71`, `MutuallyUnbiased_MixedSemantics_Canonical72`, `MutuallyUnbiased_MixedSemantics_Canonical73`, `MutuallyUnbiased_MixedSemantics_Canonical74`, `MutuallyUnbiased_MixedSemantics_Canonical75`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound126_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound30_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound51_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound76_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound77_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound78_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero818_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1008_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1013_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1124_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1167_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1179_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1264_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1268_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1269_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1536_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1562_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1649_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1703_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1709_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1781_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1783_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1786_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound427_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound428_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound445_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound446_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound447_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound448_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound456_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound462_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound463_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound482_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound817_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound902_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e` and `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`.
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

def raw8Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw85Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw85step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw85step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw86 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw86Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw86step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw86step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw86step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw86step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw87 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw87Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw87step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw87step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw88 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw88Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw88step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw88step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw88step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw88step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw89 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw89Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw89step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw89step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw90 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw90Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw90step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw90step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw90step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw90step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw91 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 2, -2], ![-2, 2, 0]]
def raw91Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw91step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw91step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw92 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw92Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw92step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw92step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw92step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw92step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw93 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw93Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw93step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw93step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw94 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw94Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw94step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw94step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw94step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw94step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw95 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw95Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw95step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw95step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw96 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw851 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw851Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw852 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw852step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw853 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw854Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw855 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw855step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw856 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw857 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw857Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw858 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw858step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw859 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw860 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw860Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw861 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw861step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw862 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw863Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw864step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw866Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw867step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw869Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw870 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw870step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw871 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw872 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw872Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw873 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw874 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw875 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw875Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw875step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw876 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw876step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw877 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw878 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw878Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw879 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw879step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw880 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw881 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw881Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw881step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw885step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw887 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw887Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw887step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw891step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw893 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw893Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw893step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw893step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw894 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw894step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw895 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]

def raw8502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8504step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8508step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8508step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8508step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8509step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8510step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8510step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8510step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8513step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8515step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8515step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8515step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8516step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8516step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw8518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8518step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8518step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8518step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw8519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8519step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8519step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw8520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw8520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw8520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw8524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw8524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8531 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8531step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8555 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8555step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8555step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8559step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8562step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8566step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8566step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8566step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8573 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-2, 1, 1]]
def raw8580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8580step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw8580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw8582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8582step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw8586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8589 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8589step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8589step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw8596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw8606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8607step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw8609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw8610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8612 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw8613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw8615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw8616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw8618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw8619step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw8622step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8622step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8622step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw8623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw8623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw8623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw8624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8624step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8624step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw8631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw8641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw8646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8646step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8646step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8684step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8684step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8684step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8685step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8686step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8690step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8694step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8695step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8697step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8698step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8699step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8700step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8700step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8701step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8702step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8703step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8703step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8704step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8705step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw8709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw8710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw8711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw8738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw8747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8749step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw8752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw8755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8755step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8755step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8755step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8758step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8759step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8760step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8760step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8760step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8760step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8760step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8761step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8762step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw8763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8763step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8763step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8763step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8764step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8764step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8764step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8766step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8766step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8767step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw8769step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8769step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8769step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8769step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw8771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw8772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw8774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8776 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8776step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw8783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8786step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8788step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw8791step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8791step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8791step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8791step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw8792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8792step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8793step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8793step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8793step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8794 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8795 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8799 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw8800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw8800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8801step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8805step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8805step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8806step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8806step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8823step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8828step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8828step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8828step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw8835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw8835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8864step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8867step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw8869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8872step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8872step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8873step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8876step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8876step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8877step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8879step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw8881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw8881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw8882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw8882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8883step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8886step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw8887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8890step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw8896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8898 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw8898Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8898step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw8898step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8898step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw8898step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw8920step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8920step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8920step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8921step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8922step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8923step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8923step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8924step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8925step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8926step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8928step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8931step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8935step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8936step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8938step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8942step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8943step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8944step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8946step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw896 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw896Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw897 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw898 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw899 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw899Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw900step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw902Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw903 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw903step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw904 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw905 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw905Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw909 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw909step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw910 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw911 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw911Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw912 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw912step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw913 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw914 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw914Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw915 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw915step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw916 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw917 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw917Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw917step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw917step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw921 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw921step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw922 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw923 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw923Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw923step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw924step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw926 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw926Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw926step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw926step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw927 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw927step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw928 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw929 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw929Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw929step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw930step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw931 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw932Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw933 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw934 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw935 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw935Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw936 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw936step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw937 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw938 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw938Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw939 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw939step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw940 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw941 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw941Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-3, -1, 4]]
def raw941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw942 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw942step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw943 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw944Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw945 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw945step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw946 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw947 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw947Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw948 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw948step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw949 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw950 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw950Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw951 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw951step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw952 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw953 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw953Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw954 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw954step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw955 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw956 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw956Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw957 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw957step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw958 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw959 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw959Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-3, 0, 3]]
def raw959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw960 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw960step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw961 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw962 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw962Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw963 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw963step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw964 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw965 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw8971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw8976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8983step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw8985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8986step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw8996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw8999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw8999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw8999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw8999step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw9001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw9001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw9001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw9005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw9006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9013 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw9013Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw9013step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9013step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9013step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9013step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw9029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw9033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw9034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw9036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw9037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9040 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9040step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9041step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9046step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9048step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9048step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9048step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9050 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9052 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw9052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw9058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9064 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9065step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9072step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9075 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9076 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw9076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw9076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw9077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw9081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw9086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw9087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9089step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9093step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9102step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9103step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9104step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9104step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw9105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9105step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9105step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9105step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw9127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9127step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9127step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9131step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9134step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9135step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9193step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw9194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw9195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw9200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw9205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9212step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9213step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw9222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9224 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw9224Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw9224step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9224step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9224step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9234step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9235 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9236 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9237step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9237step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9239 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9240 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw9243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw9244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9245 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9245step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9245step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9246 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9247 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9247step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9251 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9262step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9316step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9333step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9335step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9341step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw9346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9348 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw9348Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9348step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw9348step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9348step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9348step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw9351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw9356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9361step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9362step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9363step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9364step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9364step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9365step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9366step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9367step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9368step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9369step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9370step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9371step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9372step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9372step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9373step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9374step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9374step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9375step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9376step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9377step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9378step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9379step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9380step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9382step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9383step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9384step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9394step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9424step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9424step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9424step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9428step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw9431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9433step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw9436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9436step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9439step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw9455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9457 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw9457Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw9457step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw9457step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9457step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw9457step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9494 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9494step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9495 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9498step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9499 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw9499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw9499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9501step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 2, 2]]
def raw9504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw9506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9512step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9512step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9512step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9512step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9517step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9525step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9547step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw9548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9553step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9555step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9556step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9556step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9556step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9556step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9557step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9557step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9557step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9557step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9557step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9557step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9558step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw9559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9559step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9559step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9560step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9560step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9560step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9560step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9560step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9560step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9560step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9561step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw9561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9561step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9561step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9562step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9562step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9562step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9563step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9564step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9564step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9565step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw9565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9565step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9565step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9566step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9566step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9567step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9568step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9568step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9568step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9569step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9569step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw9569step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw9569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9570step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9570step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw9570step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw9570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9571step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9572step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9572step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw9573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw9573step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9573step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9574step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9574step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9574step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9574step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw9586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw9589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw9591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9592step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9592step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9592step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9592step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9593step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9594step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9594step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9595step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9597step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9598step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9600step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9600step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9601step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9604step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw9616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9616step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9618step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9618step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9618step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9619step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9620step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw9621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw9621step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw9621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9622step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw9625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw9625step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw9626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw9627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw9629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw9630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw9630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw9631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw9640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw9641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw9643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw9643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw9645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw9646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw9646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw9647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw9648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw9649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw9650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw9650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw9651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw9651step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw9651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw9651step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![0, -2, 2]]
def raw9652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9652step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9652step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9652step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw9652step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9653 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9653step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9654 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9654step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw9655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9655step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw9655step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw9656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw9657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw9657step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9657step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


