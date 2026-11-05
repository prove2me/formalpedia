-- Prove2me | Definitions.Def_OAIQ106E191
-- name    : OAIQ106E191
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:33:39.303966+00:00
-- url     : https://prove2.me/theorems/e9619fde-5455-45d2-8b75-2080afbffa17
-- title:
--   Definitions bundle OAIQ106E191 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2106 declarations of OpenAI's Lean: 2106 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw22843step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22843step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22843step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22843step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22844`, `OAI.MUB6.Certificate.MixedSemantics.raw22844Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22844step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22844step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22844step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22844step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22845`, `OAI.MUB6.Certificate.MixedSemantics.raw22845Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22845step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22845step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22845step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22845step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22846`, `OAI.MUB6.Certificate.MixedSemantics.raw22846Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22846step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22847`, `OAI.MUB6.Certificate.MixedSemantics.raw22847Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22847step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22847step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22847step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22847step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22848`, `OAI.MUB6.Certificate.MixedSemantics.raw22848Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step0`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step1`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step2`, `OAI.MUB6.Certificate.MixedSemantics.raw22848step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw22849`, `OAI.MUB6.Certificate.MixedSemantics.raw22849Labels` and 2066 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical0.lean), [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical17.lean), [`MutuallyUnbiased_MixedSemantics_Canonical178`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical178.lean), [`MutuallyUnbiased_MixedSemantics_Canonical179`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical179.lean), [`MutuallyUnbiased_MixedSemantics_Canonical18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical18.lean), [`MutuallyUnbiased_MixedSemantics_Canonical180`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical180.lean), [`MutuallyUnbiased_MixedSemantics_Canonical181`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical181.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1163_e`, `OAI.MUB6.Certificate.MixedSemantics.sound2593_e`, `OAI.MUB6.Certificate.MixedSemantics.sound5292_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound101_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound127_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound26_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound31_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound32_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound33_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound40_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound43_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound45_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound49_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound56_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound70_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound79_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound88_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound8_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound9_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero15_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1020_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1095_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1120_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1165_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1177_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1194_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1278_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1294_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound12_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1300_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1301_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1303_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1309_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1310_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1311_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1324_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1340_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound137_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound139_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1411_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1420_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1441_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound144_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1469_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1477_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1510_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1559_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1650_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1652_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1668_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1684_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1716_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1734_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1782_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1788_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound17_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1811_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1815_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1831_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1833_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1840_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1849_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1877_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1912_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1914_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1916_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1917_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1924_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1935_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2016_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2071_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2073_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2094_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound21_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound22_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound24_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound326_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound341_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound353_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound355_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound367_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound3_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound473_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound481_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound487_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound497_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound499_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound4_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound514_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound518_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound523_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound524_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound531_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound533_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound537_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound538_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound541_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound612_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound628_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound630_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound656_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound658_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound666_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound717_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound730_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound733_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound737_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound738_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound740_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound742_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound744_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound793_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound863_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound867_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound884_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound898_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound908_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound910_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound922_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound923_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound926_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound930_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound932_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound9_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`.
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

def raw22Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw230 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw231 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2284step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2285 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 2, -3]]
def raw2285Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw2285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2286 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2286step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2287 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2287step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2288 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2288Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw2288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2289 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2290 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2291 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2291Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw2291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2292 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2293 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2294 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2294Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2295 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2295step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2296 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2296step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2297 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2297Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2300 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2300Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2301 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2302 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2303 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2303Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2303step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2303step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw22848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22849 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw22849step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22849step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22870 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22870step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22870step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw22888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]
def raw22889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw22890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22890step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22897 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw22897Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw22897step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw22897step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22897step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw22907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22908Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![-1, 1]]
def raw22908step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22908step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw22915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw22915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22915step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw22924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 1, -3], ![1, -2, 1]]
def raw22925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw22925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22926 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![3, -3], ![-1, 1]]
def raw22926step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw22926step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22957step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22960step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw22960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw22961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw22965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22977step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22978step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22981step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw22981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw22983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw22986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22987step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw22990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22991step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw22991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22995step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw23003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23007step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw23008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw23011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw23011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw23013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw23016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw23023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw23023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]
def raw23023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23023step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

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

def raw2304 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2305 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2305step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2306 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2306Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2306step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw2306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2307 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2307step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2307step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2308 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2308step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2309 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 3, -1]]
def raw2309Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2309step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2309step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw2309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2310 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2311 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2312 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2312Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2313 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2313step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2314 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2314step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw2314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2315 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw2315Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2315step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw2315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw2315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2316 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2316step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2317 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23093step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23124 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23139 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23147 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

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

def raw23168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw23169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end


