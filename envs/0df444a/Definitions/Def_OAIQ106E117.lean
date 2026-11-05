-- Prove2me | Definitions.Def_OAIQ106E117
-- name    : OAIQ106E117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:25:52.316603+00:00
-- url     : https://prove2.me/theorems/b796f430-6dc1-47fe-902b-952d21f0bc87
-- title:
--   Definitions bundle OAIQ106E117 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7717 declarations of OpenAI's Lean: 7717 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw7285step1`, `OAI.MUB6.Certificate.MixedSemantics.raw7286`, `OAI.MUB6.Certificate.MixedSemantics.raw7286Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7286step0`, `OAI.MUB6.Certificate.MixedSemantics.raw7286step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7286step1`, `OAI.MUB6.Certificate.MixedSemantics.raw7286step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7287`, `OAI.MUB6.Certificate.MixedSemantics.raw7287Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step0`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step1`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step2`, `OAI.MUB6.Certificate.MixedSemantics.raw7287step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7288`, `OAI.MUB6.Certificate.MixedSemantics.raw7288Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7288step0`, `OAI.MUB6.Certificate.MixedSemantics.raw7288step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7288step1`, `OAI.MUB6.Certificate.MixedSemantics.raw7288step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7289`, `OAI.MUB6.Certificate.MixedSemantics.raw7289Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7289step0`, `OAI.MUB6.Certificate.MixedSemantics.raw7289step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7289step1`, `OAI.MUB6.Certificate.MixedSemantics.raw7289step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw728Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw728step0`, `OAI.MUB6.Certificate.MixedSemantics.raw728step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw728step1`, `OAI.MUB6.Certificate.MixedSemantics.raw728step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw728step2`, `OAI.MUB6.Certificate.MixedSemantics.raw728step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw729`, `OAI.MUB6.Certificate.MixedSemantics.raw7290`, `OAI.MUB6.Certificate.MixedSemantics.raw7290Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7290step0`, `OAI.MUB6.Certificate.MixedSemantics.raw7290step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw7290step1` and 7677 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical5`, `MutuallyUnbiased_MixedSemantics_Canonical56`, `MutuallyUnbiased_MixedSemantics_Canonical57`, `MutuallyUnbiased_MixedSemantics_Canonical58`, `MutuallyUnbiased_MixedSemantics_Canonical59`, `MutuallyUnbiased_MixedSemantics_Canonical6`, `MutuallyUnbiased_MixedSemantics_Canonical60`, `MutuallyUnbiased_MixedSemantics_Canonical61`, `MutuallyUnbiased_MixedSemantics_Canonical62`, `MutuallyUnbiased_MixedSemantics_Canonical63`, `MutuallyUnbiased_MixedSemantics_Canonical64`, `MutuallyUnbiased_MixedSemantics_Canonical65`, `MutuallyUnbiased_MixedSemantics_Canonical66`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1298_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1299_e`, `OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound20_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound23_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound25_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound29_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound50_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound63_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound73_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound75_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound98_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound99_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero1909_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero794_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1007_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1030_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1034_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1093_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1097_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1098_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1110_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1121_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1166_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1170_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1195_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1197_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1231_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1232_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1233_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1261_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1262_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1266_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1272_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1279_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1321_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1409_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1410_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1412_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1413_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1414_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1419_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1421_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1434_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1435_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1437_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound143_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1442_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1479_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1480_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1492_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1493_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1507_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1511_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1513_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1521_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1539_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1560_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1572_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1575_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1595_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1653_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1905_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1915_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound319_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound327_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound335_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound342_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound344_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound345_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound354_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound356_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound358_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound359_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound366_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound368_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound370_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound371_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound380_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound388_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound391_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound392_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound395_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound396_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound404_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound418_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound438_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound453_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound454_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound470_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound474_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound484_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound485_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound500_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound501_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound515_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound519_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound534_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound554_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound555_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound567_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound568_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound581_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound582_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound629_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound731_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound800_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound802_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound38_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e`.
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

def raw7Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw7step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw7step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw8 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw72Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw72step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw72step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw72step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw72step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw73 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw73Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw73step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw73step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw74 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw74Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw74step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw74step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw74step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw74step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw75 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw75Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw75step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw75step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw76 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw76Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw76step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw76step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw76step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw76step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw77 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw77Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw77step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw77step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw78 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw78Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw78step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw78step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw78step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw78step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw79 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw79Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw79step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw79step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw80 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw80Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw80step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw80step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw80step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw80step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw81 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw81Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw81step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw81step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw82 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 3, -1]]
def raw82Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw82step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw82step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw82step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw82step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw83 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![0, 1, -1], ![-2, 3, -1]]
def raw83Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw83step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw83step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw84 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw84Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw84step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw84step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw84step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw84step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw85 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw728Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw728step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw729 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw729step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw729step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw730 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw730step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw731 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw731Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw731step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw732 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw732step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw732step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw733 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw734 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw734Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw735 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw735step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw735step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw736 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw736step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw737 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw737Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw737step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw741 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw741step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw741step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw742 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw742step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw743 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw743Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw743step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw744 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw744step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw744step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw745 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw745step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw746 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw746Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw746step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw747 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw747step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw747step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw747step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw748 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw748step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw749 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 1, -2], ![-2, 4, -2]]
def raw749Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw749step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 1, 1], ![-2, -2, 4]]
def raw749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw749step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def raw749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw753 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw753step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw753step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw753step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw754 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw754step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw755 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -5, 4], ![1, 2, -3], ![-2, 3, -1]]
def raw755Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw755step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -2, 3], ![-3, 1, 2]]
def raw755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw755step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw755step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw756 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw756step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw757 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw758 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw758Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw759 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw759step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw760 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw761 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw761Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw762 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw762step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw763 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw764 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw764Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw765 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw765step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw765step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw766 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw766step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw767 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 4, -4]]
def raw767Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw767step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

def raw7286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7288 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw7288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7289 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7301step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7351step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7353step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw7356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw7357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw7358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw7359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7359step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7361step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7361step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7363step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7363step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7365step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7365step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7365step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7366step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7367Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7367step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7367step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7367step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7368step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7368step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7369Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7369step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7369step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7369step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7371Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw7371step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7371step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7372step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7372step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7373Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7373step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7374step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7375Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw7376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw7376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7377Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7377step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7379Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7379step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7387 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw7387Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7387step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7387step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw7395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw7409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7412step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7412step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7413step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7414step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7414step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7415step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7416step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7418step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7419step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7420step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7421step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7422step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7423step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7424step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7425step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7426step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7427step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7428step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7430step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7431step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw7438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7472step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7473step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7475Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7475step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7477Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7477step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw7477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw7477step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7477step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw7477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7479Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7479step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7479step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7481Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7481step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7481step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7482step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7482step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7482step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7483Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7485Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7485step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7485step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7486Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw7486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7487Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7487step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7487step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7488Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw7488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7491step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7491step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7493step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7494step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw7497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw7497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw7498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw7498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7498step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw7500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw7503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7505 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![2, -2]]
def raw7505Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw7505step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw7505step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7505step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7505step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 2, 1]]
def raw7518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw7518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw7521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw7523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7527step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7536 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7537 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7543 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7544 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7545 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7545step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7547 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7549 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7550 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7551 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw7553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7555step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7558step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7558step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7562step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![2, -2, 0]]
def raw7570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw7573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw7574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7574step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7575step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7576step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7576step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7577step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7577step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, -1, 0]]
def raw7578step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7578step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7582step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw7589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw7590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 0, -2], ![2, -2, 0]]
def raw7591step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7591step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7592step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw7594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw7595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw7595step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7595step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw7596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7596step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7596step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw7596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7596step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw7596step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7597step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7598step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7600step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7600step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7601step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7603step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7603step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw7606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7606step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7606step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7606step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7606step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7607step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7608step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7609step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7609step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw7610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7610step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7610step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7611step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7617step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7617step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7617step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7618step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw7618step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7618step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw7618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7619step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7620step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7622step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7623step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7624step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7627step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7628step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7629step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw7631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw7632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw7633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7634step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw7634step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7634step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw7634step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw7637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw7638step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw7638step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7638step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw7639step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7639step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw7639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw7642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw7643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw7643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7644step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7645step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7646step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7646step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7646step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7647step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7647step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7648step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7650step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7651step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7652step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7653step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7653step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7653step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7654step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7654step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7655step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7655step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7655step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw7656step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7656step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7656step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7656step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7657step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7658step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7659step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7659step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7659step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7659step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7660 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7661 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7662step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7662step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7662step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7663step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7663step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw7663step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7671step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw7671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7672 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7672step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7672step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7672step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7675 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7675step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7675step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7675step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7676step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7676step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7677step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7677step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7678 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7678step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7678step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7678step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7678step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7678step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7679 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7679step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7679step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7679step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7679step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7679step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw768step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw769 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw770 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw770Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw771 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw772 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw773 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw773Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw774 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw774step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw775 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw776 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw776Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw777 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw777step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw778 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw779 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw779Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw779step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw780 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw780step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw781 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw782 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw782Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw782step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw783 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw783step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw783step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw784 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw785 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw785Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw786step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw788 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw788Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw789 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw789step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw790 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw791 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw791Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw792 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw792step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw793 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw794 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw794Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw794step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw795 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw795step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw796 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw797 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw797Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw798 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw798step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw798step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw798step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw799 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw799step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw800 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw800Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw800step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw800step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw801step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw803 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw803Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw804 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw804step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw805 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw806 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw806Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw807 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw807step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw808 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw809 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw809Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw810 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw810step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw811 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw812 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw812Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw813 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw813step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw813step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw814 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw815 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw815Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw816 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw816step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw817 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw818 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw818Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw819 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw819step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw819step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw819step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw820 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw820step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw821 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw821Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw821step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw821step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw822 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw822step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw823 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw824 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw824Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw825 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw825step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw826 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw826step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw827 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw827Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw828 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw828step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw829 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw830 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw830Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw831 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw831step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw832 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw832step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw833 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw833Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw834 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw834step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw834step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw834step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw835 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw835step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw836 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw836Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw836step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw836step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw836step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw837 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw837step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw837step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw837step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw838 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw838step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw839 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw839Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw839step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw839step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw839step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw840 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw840step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw840step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw840step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw841 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw841step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw842 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw842Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw842step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw842step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw842step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw843 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw843step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw843step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw843step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw844 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw844step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw845 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw845Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw845step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw845step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw845step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw845step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw846 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw846step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw846step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw846step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw847 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw847step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw848 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw848Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw848step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw848step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw849step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw850 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7680step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7680step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7680step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7680step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7681Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7681step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7681step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7682Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7682step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7683step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7683step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7683step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7684step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7684step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7684step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7685step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw7685step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7685step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7685step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7685step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7686Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7686step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7687step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7688step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7688step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw7688step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7688step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw7688step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7688step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw7688step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7689step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7689step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7689step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7690step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7690step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7691step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7691step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7691step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7691step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7691step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7692step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw7693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7694step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw7694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-3, 1, 2]]
def raw7695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7695step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw7696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw7696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, -1, 2]]
def raw7697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7697step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw7697step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -2, 1], ![-1, -1, 2]]
def raw7698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw7698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7698step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw7698step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw7700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7731step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7762step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw7764step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7764step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7764step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7764step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw7764step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 2, -3], ![1, -2, 1]]
def raw7765step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7765step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7765step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw7765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7766step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7766step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7766step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7766step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7769step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7769step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7769step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7770step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7770step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7771step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7774step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7774step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7775step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7776step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw7776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7779step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw7779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7780step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw7780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7781step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw7781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7781step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw7781step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7782step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7783step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7784step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw7784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7785step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7785step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7785step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7785step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7785step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7785step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7786step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7786step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7786step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw7786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7787step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7788step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7789step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 3, -3], ![3, -4, 1]]
def raw7790step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 3, -3], ![3, -4, 1]]
def raw7790step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7790step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7790step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7790step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw7790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7791step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw7791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, 1, -3], ![2, -3, 1]]
def raw7795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7795step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw7795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 2, -3], ![3, -4, 1]]
def raw7796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7796step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw7796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7797 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![3, -3], ![-1, 1]]
def raw7797step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![3, -3], ![-1, 1]]
def raw7797step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw7797step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7797step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw7797step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw7799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 3, -3], ![2, -3, 1]]
def raw7800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7800step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 2, -3], ![1, -2, 1]]
def raw7801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw7801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw7804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw7804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw7805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, 1, -3], ![1, -2, 1]]
def raw7805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7805step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw7805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw7809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7816step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7826step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7826step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7831step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7832step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7832step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7832step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7832step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7833step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7833step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7833step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7833step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7834step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7834step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7834step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7839step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw7839step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw7839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7839step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7839step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7849step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7854step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7854step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw7859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7864step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7865step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7865step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw7865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7865step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7865step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7867step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7869step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7870step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7871step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7872step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7873step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7874step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7875step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7875step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7876step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7878step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7882step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7882step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7886step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7887step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7887step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw7892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7901step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7918step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7919step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7919step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7919step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7920step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7922step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7923step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7924step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7925step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7926step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7927step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7927step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7927step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7927step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7927step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7928step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7929step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7929step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7929step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7930step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7930step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7930step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7931 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7932 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7933 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7934 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7935 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7938 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7939 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7940 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7940step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7941 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7942 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7942step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7942step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7942step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7943 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7944 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7945 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7945step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7945step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7945step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7945step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7946 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7946step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7947 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7947step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7947step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7949 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7949step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7949step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7949step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7951 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7952 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7953 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7953step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7953step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7953step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7953step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7953step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7954 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7955step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7955step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7955step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7955step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7955step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7956step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7958step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw7958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw7959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw7963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw7964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7964step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw7964step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7972step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7976step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7976step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7980step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7980step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7996step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw8000step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw8001step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8004step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8004step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw8005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw8005step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8005step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw8005step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8007step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8009step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8010step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8010step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8012step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8013step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8015step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8017step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw8020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8020step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8020step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8020step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8020step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8021step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8022step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8025step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8027step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8029step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw8030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw8030step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw8031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw8031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw8031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8031step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw8031step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8034step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw8035step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8035step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw8035step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8036step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8040step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw8045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8047step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw8049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw8050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw8050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw8050step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8051step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw8055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw8055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw8056step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8057step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw8060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw8060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw8061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw8061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw8061step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8061step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw8061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8062 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8064step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8067 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw8103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8103step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw8125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw8129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8134step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8134step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8148step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8149step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8149step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8149step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw8150step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw8150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8151step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8152step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8153step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw8154step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8154step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8154step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8154step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8155step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8155step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8155step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8158step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8166 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8166step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw8174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8232step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8233step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8237step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8238step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8239step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8239step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8239step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8239step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8239step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8241step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8242step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw8243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw8243step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8243step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw8243step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8246step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw8247step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8247step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw8247step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8247step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw8247step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8248step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw8250step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw8250step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8251step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw8267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw8272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8300 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8301 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8302 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8307 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8307step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8308 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8309 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw8309step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8309step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8309step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8309step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8310 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8311 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw8311step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8311step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw8311step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8312 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw8312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw8312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw8314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw8314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8315 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8320 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8320step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8321step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw8378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw8381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw8383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw8383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -2, 3], ![-3, 2, 1]]
def raw8384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw8385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8386step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8386step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8387Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8387step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8387step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8387step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8387step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8388step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw8388step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8388step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8388step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8388step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8390step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8390step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8390step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8393step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8393step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8396step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8396step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8397step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8397step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8398step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8401step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8401step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8401step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8401step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw8404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8405step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8405step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8405step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw8406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw8406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw8409step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw8409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw8410step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8411step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw8411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8411step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8411step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw8411step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw8414step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw8414step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8414step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8414step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw8414step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw8415step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw8419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw8421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8422 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]
def raw8422step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8422step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8422step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw8433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw8465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8469step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw8494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8498step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


