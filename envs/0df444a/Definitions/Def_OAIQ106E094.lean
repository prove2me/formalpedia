-- Prove2me | Definitions.Def_OAIQ106E094
-- name    : OAIQ106E094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:07:50.964296+00:00
-- url     : https://prove2.me/theorems/ef9e2ad2-d19b-4f75-9281-b2888bf6d0be
-- title:
--   Definitions bundle OAIQ106E094 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7303 declarations of OpenAI's Lean: 7303 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.raw18020step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18021`, `OAI.MUB6.Certificate.MixedSemantics.raw18021Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step3`, `OAI.MUB6.Certificate.MixedSemantics.raw18021step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18022`, `OAI.MUB6.Certificate.MixedSemantics.raw18022Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step3`, `OAI.MUB6.Certificate.MixedSemantics.raw18022step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18023`, `OAI.MUB6.Certificate.MixedSemantics.raw18023Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step3`, `OAI.MUB6.Certificate.MixedSemantics.raw18023step3Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18024`, `OAI.MUB6.Certificate.MixedSemantics.raw18024Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step0`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step0Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step1`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step1Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step2`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step2Labels`, `OAI.MUB6.Certificate.MixedSemantics.raw18024step3` and 7263 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Canonical1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical1.lean), [`MutuallyUnbiased_MixedSemantics_Canonical14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical14.lean), [`MutuallyUnbiased_MixedSemantics_Canonical140`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical140.lean), [`MutuallyUnbiased_MixedSemantics_Canonical141`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical141.lean), [`MutuallyUnbiased_MixedSemantics_Canonical142`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical142.lean), [`MutuallyUnbiased_MixedSemantics_Canonical143`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical143.lean), [`MutuallyUnbiased_MixedSemantics_Canonical144`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical144.lean), [`MutuallyUnbiased_MixedSemantics_Canonical145`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical145.lean), [`MutuallyUnbiased_MixedSemantics_Canonical146`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical146.lean), [`MutuallyUnbiased_MixedSemantics_Canonical147`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical147.lean), [`MutuallyUnbiased_MixedSemantics_Canonical148`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Canonical148.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.MixedSemantics.sound1475_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1477_e`, `OAI.MUB6.Certificate.MixedSemantics.sound1478_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound103_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound111_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound116_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound117_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound119_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound123_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound128_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound131_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound19_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound28_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound34_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound38_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound39_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound41_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound42_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound44_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound46_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound58_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound59_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound5_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound60_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound61_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound62_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound72_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound80_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound81_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound82_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound91_e`, `OAI.MUB6.Certificate.MixedSourceBridge.chunkSound92_e`, `OAI.MUB6.Certificate.MixedSourceBridge.reducedZero14_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound0_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound109_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1114_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1130_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound113_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound115_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1191_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound125_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1312_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1433_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1505_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1508_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1516_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound151_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1593_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1648_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1654_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1655_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1672_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1673_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1679_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1686_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1687_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1702_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1708_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1710_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1715_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1723_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1780_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1784_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1822_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1835_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1838_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1839_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1844_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1853_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1855_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1858_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1864_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1871_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1872_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1873_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1904_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1944_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1960_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1984_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1990_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1993_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1995_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1998_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1999_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound1_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2002_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2006_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2018_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2019_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2021_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2023_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2033_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2036_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2059_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2060_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2066_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2067_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2075_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2096_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2099_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2107_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound2108_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound267_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound339_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound343_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound357_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound365_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound369_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound417_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound444_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound452_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound483_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound542_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound545_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound546_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound551_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound553_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound564_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound566_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound570_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound578_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound580_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound584_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound587_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound588_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound589_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound599_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound719_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound735_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound749_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound787_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound789_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound795_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound799_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound813_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound865_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound936_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound937_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound938_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound939_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound940_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound941_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound942_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound947_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound948_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound949_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound950_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound951_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound952_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound953_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound954_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound956_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound957_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound958_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound959_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound962_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound963_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound964_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound965_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound966_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound967_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound968_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound970_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound971_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound972_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound973_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound974_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound975_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound976_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound97_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound983_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound988_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound991_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound992_e`, `OAI.MUB6.Certificate.MixedSourceBridge.rowSound99_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`.
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

def raw180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw181 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw181step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw181step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw183step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw187step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw188 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw189 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1802Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1803 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1804 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1805 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1805Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1806 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1807 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1808 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1808Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw1808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1809 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1810 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1811 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1811Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1811step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1812 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1813 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1814 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1814Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1815 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1816 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1817 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1817Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw1817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1818 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1819 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1820 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1820Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1821 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1822 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1823 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1823Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw1823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1824 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1825 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1826 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1826Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1826step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw1826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1827 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1828 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1829 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1829Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw1829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1830 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1830step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1830step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1831 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1831step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1832 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1832Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw1832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1835Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1848 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1849 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1850 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1850Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1863 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1864 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1865 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1865Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1887step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1889Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1889step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1890step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1892Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1893step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1895Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1896step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1898Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1899 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical140
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18023step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw18026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1]]
def raw18027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18028step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw18028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18028step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18028step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw18029step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw18029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw18031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw18032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1]]
def raw18032step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18033step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw18034step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw18034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw18036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw18037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw18037step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18037step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 3, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18038step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18041step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18041step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18042step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18043step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18043step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18044step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18045step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw18046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical141
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18049step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18054step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18057step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18059step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -3, 1], ![1, 0, -1]]
def raw18062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18062step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, 1, 1], ![-2, -1, 3]]
def raw18064step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18065step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18066step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![3, -2, -1]]
def raw18067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18067step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18068step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18071step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18073step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18076step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18080step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18088step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18091step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18092step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18104step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18105step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw18105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18111step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18113step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw18132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18134step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw18137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18138step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18144step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18147step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18148step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18151step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18163step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical142
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw18176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw18178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18183step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18186step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18187step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18189step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18192step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18194step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18202step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18206step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw18207step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18224step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw18233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18241step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18251step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18264step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18269step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18271step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18273step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18274step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18278step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18286step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw18287step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18290step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2]]
def raw18297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18297step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw18310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18310step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18310step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw18312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18322step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw18325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw18330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw18333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw18334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18335step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18335step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18336step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw18336step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18336step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18336step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18337step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18337step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18338step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18338step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18339step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw18339step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18340step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18340step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18340step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18340step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw18341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18341step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw18341step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18341step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18341step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw18341step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18342step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18342step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw18342step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw18342step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18342step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw18342step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18343step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18343step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18343step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18343step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18343step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw18344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18344step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw18344step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw18344step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18344step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw18344step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18347step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18347step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18348step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18353step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18357step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18359step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18360step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18361step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18361step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18362step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18363step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18363step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18370step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18372step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18372step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18374step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw18376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18376step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw18380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18387step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18387step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18387step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18391step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw18397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18408step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18410step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18411 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18411step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18412 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18413step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18413step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18414step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18417step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18417step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18418step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18418step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18419 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18423step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18423step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18423step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18424step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18428step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18429step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical144
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18433step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18434step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18435step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18436step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18437step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18444step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18452step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18453step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18454step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18455step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18456step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18457step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18458step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18459step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18460step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18473step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18474step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18478step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18479step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18483step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18484step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18486step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18488step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18489step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18490step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18495step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18500step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw18501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw18501step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw18505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18511step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18512step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18514step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18515step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18517step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18518step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18519step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18521step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18522step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18523step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18525step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18527step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18528step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18529step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18530step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18531step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18532step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18533step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18539step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18545step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18549step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18550step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw18552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18574step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18575step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18576step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18577step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18578step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18586step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18587step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18596step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18602step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18608step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw18610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18611step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18612step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18613step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18614step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18615step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18616step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18617step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18618step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18619step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18622 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw18625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18635step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18645step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw18653step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18658step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18662step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18674step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18678step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18678step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18679step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18679step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18679step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw18680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw18680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18682step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw18683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw18683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18683step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18685step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18685step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18687step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18687step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18688step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18689step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18689step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18689step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18690step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18691step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18691step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18692step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18695step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18696step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18697step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18698step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18699step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18700step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18701step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18702step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18703step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18704step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18753step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18766step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18766step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18775step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18780step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18781step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw18782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18783step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18784step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw18786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18793step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18794step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw18798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18804step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18805step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18806step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18806step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18807step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18807step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18808step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18812step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18812step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18813step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18814step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18815step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18816step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18817step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18817step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18817step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18818step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18819step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18820step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18820step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18820step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18821step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18822step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18823step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18824step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18825step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18825step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18825step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18826step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18827step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18828step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18832step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18841step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw18842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18863 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18864 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18864step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18866 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18867step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18868step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18869step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18872step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18873 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18873step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18874step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18875 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18875step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18876 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18876step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18877 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18877step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18878step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18878step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18878step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18879step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18879step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18880step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18881 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18882step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18883step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18883step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18883step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18884 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18885step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw18887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18888step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18888step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18889step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18889step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18890step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18891step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18892step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18896 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18897 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw18912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18913 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw18916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw18917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18924step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18925step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18925step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18926step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18927step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18929step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18930step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18931step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18932step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18933step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18935step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18941step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18943step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18946step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18946step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18946step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18948step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18949step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18952step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw18968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw18968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw18968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18969step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18972step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18975step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18983step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18984step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18986step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18987step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18987step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18989step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18990step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18991step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end


